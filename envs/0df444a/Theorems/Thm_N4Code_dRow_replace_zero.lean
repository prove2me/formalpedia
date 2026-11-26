-- Prove2me | Theorems.Thm_N4Code_dRow_replace_zero
-- name    : N4Code.dRow_replace_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:06.644749+00:00
-- url     : https://prove2.me/theorems/e2a1b9b3-29af-4786-9934-1cba8174d524
-- title:
--   N4 Code: d Row replace zero
-- statement:
--   Replacing the 0-column at t by s' changes row i only if s' has bit 1 there;
--   then the new distance is the old distance at the flipped word.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L263-L291
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L263-L291

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dRow_replace_zero {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (hcol : C t = col0)
    (y : Word n) :
    ∀ i : Fin 4, dRow (replaceColumn C t s') i y =
      if s' i then dRow C i (flipBit t y) else dRow C i y := by sorry
