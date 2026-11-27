-- Prove2me | Theorems.Thm_MohP3_Wt_exists_wOrd_limit
-- name    : MohP3.Wt.exists_wOrd_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:19.274663+00:00
-- url     : https://prove2.me/theorems/6256ab26-925d-4366-aa3f-1ab6ed4c3738
-- title:
--   Wt: exists w Ord limit
-- statement:
--   The Wt construction uses the exists w Ord limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L199-L214
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L199-L214

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

theorem MohP3.Wt.exists_wOrd_limit (g : ℕ → MvPowerSeries (Fin 3) k) (s₀ : ℕ)
    (hg : ∀ s, WOrd (g s) (s - s₀)) :
    ∃ G : MvPowerSeries (Fin 3) k, ∀ M, WOrd (G - ∑ s ∈ Finset.range M, g s) (M - s₀) := by sorry
