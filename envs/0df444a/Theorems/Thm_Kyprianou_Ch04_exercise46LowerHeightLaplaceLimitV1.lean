-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46LowerHeightLaplaceLimitV1
-- name    : Kyprianou.Ch04.exercise46LowerHeightLaplaceLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:31:41.076385+00:00
-- url     : https://prove2.me/theorems/88c07a35-16e4-5a8f-8987-3a330eec7075
-- title:
--   Dominated convergence of positive-height Laplace payoffs
-- statement:
--   The Laplace payoffs are almost surely bounded by one and converge by continuity.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46LowerHeightLaplaceLimitV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A : Nat → Omega → Real) (J : Omega → Real)
    (phi : Real) (hphi : 0 ≤ phi)
    (hA : ∀ n, AEMeasurable (A n) P)
    (hpos : ∀ n, ∀ᵐ w ∂P, 0 < A n w)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun n => A n w) atTop (nhds (J w))) :
    Tendsto (fun n => ∫ w, Real.exp (-phi * A n w) ∂P) atTop
      (nhds (∫ w, Real.exp (-phi * J w) ∂P)) := by
  sorry
