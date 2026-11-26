-- Prove2me | Theorems.Thm_N4Code_wordTransform_bijective
-- name    : N4Code.wordTransform_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:50.593871+00:00
-- url     : https://prove2.me/theorems/85bf734b-6bec-467a-b981-95c67bbf5a06
-- title:
--   N4 Code: word Transform bijective
-- statement:
--   The word transform is bijective.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L151-L156
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L151-L156

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

theorem N4Code.wordTransform_bijective {n : ℕ} (p : Equiv (Fin n) (Fin n)) (f : Fin n → Bool) :
    Function.Bijective (wordTransform p f) := by sorry
