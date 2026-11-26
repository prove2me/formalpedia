-- Prove2me | Theorems.Thm_N4Code_wordTransform_inv_left
-- name    : N4Code.wordTransform_inv_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:46.436978+00:00
-- url     : https://prove2.me/theorems/6a6906ef-f988-5d27-9288-7494c92c5f68
-- title:
--   N4 Code: word Transform inv left
-- statement:
--   The N4 Code construction uses the word Transform inv left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L140-L143
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L140-L143

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

theorem N4Code.wordTransform_inv_left {n : ℕ} (p : Equiv (Fin n) (Fin n)) (f : Fin n → Bool) (y : Word n) :
    wordTransform p f (wordTransformInv p f y) = y := by sorry
