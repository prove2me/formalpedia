-- Prove2me | Theorems.Thm_FramedDescriptor_two_input_symbols_and_output_one_need_bits
-- name    : FramedDescriptor.two_input_symbols_and_output_one_need_bits
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T22:02:21.072883+00:00
-- url     : https://prove2.me/theorems/e1516691-7fcc-578f-acd2-d64e7ec73305
-- title:
--   A framed transition table reading both bit values and emitting one requires 49 bits
-- statement:
--   Suppose a parsed transition table has an input-zero row, an input-one row, and an output-one row. The output row may be one of the two input rows. Then the original bit string has length at least 49. The bound also holds for noncanonical parser inputs.
-- source:
--   Framed universal-machine transition encoding in the Prove2Me Complexitylib definition library.

import Definitions.Def_FramedDescriptorBitWidth

open FramedDescriptor

theorem FramedDescriptor.two_input_symbols_and_output_one_need_bits (w : List Bool)
    (inputZero : ∃ u ∈ rows w, inputSymbol u = some 0)
    (inputOne : ∃ v ∈ rows w, inputSymbol v = some 1)
    (output : ∃ z ∈ rows w, outputSymbol z = some 1) :
    49 ≤ w.length := by sorry
