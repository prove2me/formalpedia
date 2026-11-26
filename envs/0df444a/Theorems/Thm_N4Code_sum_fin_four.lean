-- Prove2me | Theorems.Thm_N4Code_sum_fin_four
-- name    : N4Code.sum_fin_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:53.740528+00:00
-- url     : https://prove2.me/theorems/a40cc1df-6780-5f14-ba5f-f60003820cd1
-- title:
--   N4 Code: sum fin four
-- statement:
--   Expand a sum over `Fin 4` into its four terms.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L267-L274
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L267-L274

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Definitions.Def_N4Code_Basic
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code

theorem N4Code.sum_fin_four (f : Fin 4 → ℕ) :
    (∑ k : Fin 4, f k) = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ := by sorry
