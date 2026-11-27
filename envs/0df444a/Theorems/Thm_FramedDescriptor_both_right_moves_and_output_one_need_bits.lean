-- Prove2me | Theorems.Thm_FramedDescriptor_both_right_moves_and_output_one_need_bits
-- name    : FramedDescriptor.both_right_moves_and_output_one_need_bits
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T22:13:12.948251+00:00
-- url     : https://prove2.me/theorems/59f46e92-f8b4-5c12-a107-5d4100192b2e
-- title:
--   A framed transition table that moves right on both bits and can emit one requires 59 bits
-- statement:
--   Suppose a parsed transition table has a row reading zero and moving the input head right, a row reading one and moving the input head right, and a row emitting one. The emitting row may coincide with either reading row. Moving the input head right means that the decoded direction field starts with a true bit. Then the original bit string has length at least 59, including for inputs that are not canonically framed.
-- source:
--   Framed universal-machine transition encoding in the Prove2Me Complexitylib definition library.

import Definitions.Def_FramedDescriptorBitWidth

open Turing.MultiTapeTM FramedDescriptor

theorem FramedDescriptor.both_right_moves_and_output_one_need_bits (w : List Bool)
    (zeroRight : ∃ u ∈ rows w, inputSymbol u = some 0 ∧ (unframe (dropFrame u)).headD false = true)
    (oneRight : ∃ v ∈ rows w, inputSymbol v = some 1 ∧ (unframe (dropFrame v)).headD false = true)
    (output : ∃ z ∈ rows w, outputSymbol z = some 1) :
    59 ≤ w.length := by sorry
