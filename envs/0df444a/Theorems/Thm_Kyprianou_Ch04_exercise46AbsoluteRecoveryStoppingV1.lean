-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46AbsoluteRecoveryStoppingV1
-- name    : Kyprianou.Ch04.exercise46AbsoluteRecoveryStoppingV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:26:16.771564+00:00
-- url     : https://prove2.me/theorems/8ec07a5a-84cf-5b1e-8b94-e5be91f4e12f
-- title:
--   Absolute strict recovery clock is a stopping time
-- statement:
--   Use dense sampled stopping times and right continuity to identify the unrestricted clock.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46AbsoluteRecoveryStoppingV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A) :
    let R : Omega → WithTop NNReal := fun w =>
      ⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧
        (((A w).untopD 0 : NNReal) : Real) < L.X r w
        then (r : WithTop NNReal) else ⊤
    IsStoppingTime G.rightCont R := by
  sorry
