-- Prove2me | Theorems.Thm_N4Code_flipTwoBits_involutive
-- name    : N4Code.flipTwoBits_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:44.796247+00:00
-- url     : https://prove2.me/theorems/f4d2523c-7ae4-44bf-86e8-5aebc0c98b81
-- title:
--   N4 Code: flip Two Bits involutive
-- statement:
--   F₂ is an involution.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L27-L30
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L27-L30

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.flipTwoBits_involutive {n : ℕ} (t₁ t₂ : Fin n) (y : Word n) :
    flipTwoBits t₁ t₂ (flipTwoBits t₁ t₂ y) = y := by sorry
