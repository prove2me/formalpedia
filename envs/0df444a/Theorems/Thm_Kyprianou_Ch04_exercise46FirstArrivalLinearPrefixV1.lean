-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FirstArrivalLinearPrefixV1
-- name    : Kyprianou.Ch04.exercise46FirstArrivalLinearPrefixV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:43:20.820738+00:00
-- url     : https://prove2.me/theorems/c5211234-4667-4c12-9314-42de341dfadd
-- title:
--   Unit drift until first physical arrival, with global drift bound
-- statement:
--   The finite-activity exact jump-sum representation vanishes before the first arrival. Monotonicity of the drift deficit gives the global bound.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FirstArrivalLinearPrefixV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation) (hDrift : L.drift = 1)
    (hFinite : L.ν (Iio (0 : Real)) < ⊤)
    (a : Omega → NNReal)
    (hBefore : ∀ᵐ w ∂P, ∀ u : NNReal, 0 < u → u < a w →
      L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u) :
    ∀ᵐ w ∂P, (∀ s : NNReal, s < a w → L.X s w = (s : Real)) ∧
      (∀ s : NNReal, L.X s w ≤ (s : Real)) := by
  sorry
