-- Prove2me | Theorems.Thm_Kyprianou_Ch03_canonicalClippedLawEqOfFiniteMarginalsV1
-- name    : Kyprianou.Ch03.canonicalClippedLawEqOfFiniteMarginalsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:04:23.006252+00:00
-- url     : https://prove2.me/theorems/c0a40093-6d7f-44e1-a491-72e2977c39a2
-- title:
--   Equality of full product laws after clipping to a finite horizon
-- statement:
--   All finite-dimensional marginals of the clipped paths agree: restrict a finite coordinate set to its subset within the horizon and fill all other coordinates with zero. Uniqueness of finite measures on the product cylinder pi-system gives equality of the clipped product laws.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; support for canonicalProbabilityFromMarginalLimitV1

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.canonicalClippedLawEqOfFiniteMarginalsV1
    {Ω : Type} [MeasurableSpace Ω]
    (X : NNReal → Ω → ℝ) (hX : ∀ u, Measurable (X u))
    (D : Measure Ω) (hD : D Set.univ = 1)
    (M : Measure (NNReal → ℝ)) (hM : M Set.univ = 1)
    (t : NNReal)
    (hMarg : ∀ J : Finset NNReal, (∀ j ∈ J, j ≤ t) →
      M.map (fun path (j : J) => path j.val) =
        D.map (fun w (j : J) => X j.val w)) :
    M.map (fun path u => if u ≤ t then path u else 0) =
      D.map (fun w u => if u ≤ t then X u w else 0) := by sorry
