#!/bin/bash
# This bash script reads all files in the ./_symbols directory and replaces filenames with new [uid].js to invalidate cache.
# Before replacing the filenames, it searches all files in the ./ directory and text replaces the occurences of old script filenames with new script filenames.

# Set locale to handle non-ASCII characters
export LC_ALL=C.UTF-8
export LANG=C.UTF-8

# Function to generate a unique identifier
generate_uid() {
  echo $(uuidgen)
}

# Directory containing the symbol files
SYMBOLS_DIR="./_symbols"

# Process each file in the SYMBOLS_DIR
for old_file in "$SYMBOLS_DIR"/*; do
  if [ -f "$old_file" ]; then
    # Get the base name of the old file
    old_filename=$(basename "$old_file")
    
    # Generate a new UID and construct the new filename
    new_uid=$(generate_uid)
    new_filename="${new_uid}.js"
    
    # Find all files in the ./ directory and replace occurrences of the old filename with the new filename
    find ./ -type f -exec grep -Il "$old_filename" {} \; | while read -r file; do
      sed -i "" "s/$old_filename/$new_filename/g" "$file"
    done
    
    # Rename the old file to the new filename
    mv "$old_file" "$SYMBOLS_DIR/$new_filename"
    
    echo "Replaced $old_filename with $new_filename"
  fi
done

echo "Filename replacement and content update completed."
