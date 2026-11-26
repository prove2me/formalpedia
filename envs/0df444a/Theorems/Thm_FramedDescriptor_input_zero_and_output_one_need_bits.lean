-- Prove2me | Theorems.Thm_FramedDescriptor_input_zero_and_output_one_need_bits
-- name    : FramedDescriptor.input_zero_and_output_one_need_bits
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T22:00:45.890713+00:00
-- url     : https://prove2.me/theorems/8382cea7-cd2c-4beb-bd8c-89cef7d9193e
-- title:
--   A framed transition table that reads zero and emits one requires 29 bits
-- statement:
--   Suppose a parsed transition table has a row whose input symbol is zero, and a row whose output symbol is one. These can be the same row. The original bit string has length at least 29. The bound applies to every parser input, including strings without a canonical encoding.
-- source:
--   Framed universal-machine transition encoding in the Prove2Me Complexitylib definition library.

import Definitions.Def_FramedDescriptorBitWidth

open FramedDescriptor

theorem FramedDescriptor.input_zero_and_output_one_need_bits (w : List Bool)
    (input : ∃ u ∈ rows w, inputSymbol u = some 0)
    (output : ∃ v ∈ rows w, outputSymbol v = some 1) :
    29 ≤ w.length := by sorry
