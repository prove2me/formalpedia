-- Prove2me | Theorems.Thm_LovaszLocalLemma_lll
-- name    : LovaszLocalLemma.lll
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:27:28.133568+00:00
-- url     : https://prove2.me/theorems/51cf58a3-9d97-52f8-9e05-3c2c5a4a57d2
-- title:
--   Lovasz Local Lemma: lll
-- statement:
--   **The Lovász Local Lemma, general form.**
--
--   Source: https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/Solution.lean#L40-L46
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/Solution.lean#L40-L46

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Definitions.Def_LovaszLocalLemma_Solution
public import Theorems.Thm_LocalLemma_lll

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LovaszLocalLemma

theorem LovaszLocalLemma.lll {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (Γ : SimpleGraph (Fin n))
    [DecidableRel Γ.Adj] (hΓ : IsDependencyGraph μ A Γ) (x : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1)
    (hP : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ Γ.neighborFinset i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ μ.real (⋂ i, (A i)ᶜ) := by sorry
