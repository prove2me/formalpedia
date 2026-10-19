-- Prove2me | Theorems.Thm_IntMul_Kappa_binary_val_append
-- name    : IntMul.Kappa.binary_val_append
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T22:00:33.118315+00:00
-- url     : https://prove2.me/theorems/b2b96a31-0570-4a92-9a4d-44597d71b047
-- title:
--   Concatenation law for the multiplication model's MSB-first bit encoding
-- statement:
--   For the exact IntMul.val defined by a left fold in base two on MSB-first Boolean words, concatenating two bit strings obeys val(x++y)=2^(length y)·val(x)+val(y). This identity is foundational for correctly reading split input records, proving output padding, converting between binary string conventions and verifying the tape-level arithmetic implementation. The result uses no multiplication speedup assumptions and is valid for empty strings and leading zeros.
-- source:
--   IntMul_MultitapeModel platform definition of val, UUID 47ff1689-4e87-4af2-9406-674787e32429; fundamental binary concatenation formula needed for uniform integer multiplication encoding and output exactness.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

theorem IntMul.Kappa.binary_val_append (x y : List Bool) :
    IntMul.val (x ++ y) = 2 ^ y.length * IntMul.val x + IntMul.val y := by sorry
