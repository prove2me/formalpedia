-- Prove2me | Theorems.Thm_Kyprianou_Ch02_campbellMomentL2BoundFromEventuallyBoundedMarksV1
-- name    : Kyprianou.Ch02.campbellMomentL2BoundFromEventuallyBoundedMarksV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:16:55.521928+00:00
-- url     : https://prove2.me/theorems/1dcf5811-f6d7-4487-885f-5e2712e9c8e3
-- title:
--   Campbell second moments and an eventual finite mark L2 bound control the Poisson integral L2 liminf
-- statement:
--   For real simple mark integrands on a finite-intensity region, an eventual uniform finite L2 mark bound and the exact Campbell quadratic-moment identity imply that the associated square-integrable random variables have bounded L2 norms eventually, hence a finite liminf. This is an analytic Poisson second-moment transfer lemma; no stochastic independence statement is hidden in the conclusion.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.9: second-moment formula and L2 bound.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.campbellMomentL2BoundFromEventuallyBoundedMarksV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (B : Set ℝ) (hfinite : ν B < ⊤)
    (f : ℕ → SimpleFunc ℝ ℝ) (X : ℕ → Ω → ℝ)
    (hrawL2 : ∀ n, MemLp (X n) 2 P)
    (hmark : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ᶠ n in Filter.atTop,
      eLpNorm (fun x : ℝ => (f n) x) 2 (ν.restrict B) ≤ C)
    (t : ℝ≥0)
    (hCampbell : ∀ n,
      (∫ ω, (X n ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ x in B, ((f n) x) ^ 2 ∂ν) +
          ((t : ℝ) * (∫ x in B, (f n) x ∂ν)) ^ 2) :
    Filter.liminf (fun n => eLpNorm (X n) 2 P)
      Filter.atTop < ⊤ := by sorry
