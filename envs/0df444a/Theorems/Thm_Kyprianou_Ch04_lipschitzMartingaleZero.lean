-- Prove2me | Theorems.Thm_Kyprianou_Ch04_lipschitzMartingaleZero
-- name    : Kyprianou.Ch04.lipschitzMartingaleZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:39:46.451711+00:00
-- url     : https://prove2.me/theorems/0235ae73-81f9-42f6-85f5-06d06d3936bd
-- title:
--   lipschitzMartingaleZero
-- statement:
--   A uniformly Lipschitz martingale starting at zero is zero at every deterministic time.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A uniformly Lipschitz martingale starting at zero is zero at every deterministic time. -/
theorem Kyprianou.Ch04.lipschitzMartingaleZero {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : NNReal → Omega → ℝ) (hM : Martingale M F P)
    (h0 : ∀ᵐ w ∂P, M 0 w = 0) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ s t : NNReal, s ≤ t → ∀ᵐ w ∂P,
      |M t w - M s w| ≤ C * ((t : ℝ) - (s : ℝ))) :
    ∀ t : NNReal, M t =ᵐ[P] 0 := by
  sorry
