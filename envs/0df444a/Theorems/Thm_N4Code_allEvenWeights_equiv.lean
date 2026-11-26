-- Prove2me | Theorems.Thm_N4Code_allEvenWeights_equiv
-- name    : N4Code.allEvenWeights_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:54.004175+00:00
-- url     : https://prove2.me/theorems/46a6e4fb-6feb-4f22-baea-99c7a22422a8
-- title:
--   N4 Code: all Even Weights equiv
-- statement:
--   The even-weight property is invariant under equivalence.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L333-L348
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L333-L348

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.allEvenWeights_equiv {n : ℕ} (C C' : Code n) (h : Equivalent C C') :
    allEvenWeights C ↔ allEvenWeights C' := by sorry
