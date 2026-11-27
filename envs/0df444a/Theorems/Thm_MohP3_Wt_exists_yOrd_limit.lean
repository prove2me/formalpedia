-- Prove2me | Theorems.Thm_MohP3_Wt_exists_yOrd_limit
-- name    : MohP3.Wt.exists_yOrd_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:15.912031+00:00
-- url     : https://prove2.me/theorems/d7a7c5e8-321f-5499-8b5b-77dd10da3867
-- title:
--   Wt: exists y Ord limit
-- statement:
--   The Wt construction uses the exists y Ord limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L182-L197
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L182-L197

module
public import Mathlib
public import Definitions.Def_MohP3_Order
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]

theorem MohP3.Wt.exists_yOrd_limit (g : ℕ → PowerSeries k) (s₀ : ℕ)
    (hg : ∀ s, YOrd (g s) (s - s₀)) :
    ∃ G : PowerSeries k, ∀ M, YOrd (G - ∑ s ∈ Finset.range M, g s) (M - s₀) := by sorry
