-- Prove2me | Theorems.Thm_LocalLemma_lll_cond
-- name    : LocalLemma.lll_cond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:21:14.082128+00:00
-- url     : https://prove2.me/theorems/9dedae04-a32a-54f1-8e38-8b4be3fde586
-- title:
--   Local Lemma: lll cond
-- statement:
--   The main inductive claim of the Local Lemma, in product form.
--
--   Source: https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean#L109-L157
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean#L109-L157

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma

theorem LocalLemma.lll_cond {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (Γ : SimpleGraph (Fin n))
    [DecidableRel Γ.Adj] (hΓ : IsDependencyGraph μ A Γ) (x : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1)
    (hP : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ Γ.neighborFinset i, (1 - x j)) :
    ∀ S : Finset (Fin n), ∀ i ∉ S, μ.real (avoid A S ∩ A i) ≤ x i * μ.real (avoid A S) := by sorry
