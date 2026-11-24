-- Prove2me | Theorems.Thm_MomentComparison_pair_count_ge
-- name    : MomentComparison.pair_count_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:28:15.547014+00:00
-- url     : https://prove2.me/theorems/ced546ee-5c0e-4149-a913-db678035bac6
-- title:
--   Moment Comparison: pair count ge
-- statement:
--   To form two (m)-sets with symmetric difference (U), choose which half of (U)
--   lies in the first set, and independently choose a common subset of its complement.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Counting.lean#L16-L70
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Counting.lean#L16-L70

module
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Prod
public import Definitions.Def_MomentComparison_Counting
set_option autoImplicit true
@[expose] public section
public section
open scoped symmDiff
open MomentComparison

theorem MomentComparison.pair_count_ge {α : Type*} [Fintype α] [DecidableEq α]
    (m k : ℕ) (hkm : k ≤ m) (U : Finset α) (hU : U.card = 2 * k) :
    (2 * k).choose k * (Fintype.card α - 2 * k).choose (m - k) ≤
      (((Finset.univ : Finset α).powersetCard m ×ˢ
        (Finset.univ : Finset α).powersetCard m).filter (fun p => p.1 ∆ p.2 = U)).card := by sorry
