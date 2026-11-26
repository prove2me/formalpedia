-- Prove2me | Theorems.Thm_Kyprianou_Ch04_overloadedInput_tendsto_atBot
-- name    : Kyprianou.Ch04.overloadedInput_tendsto_atBot
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T15:15:45.310614+00:00
-- url     : https://prove2.me/theorems/7f7f987e-e008-4a0f-bb79-f5f7bbcd24a2
-- title:
--   Overloaded bounded-variation Levy input drifts to minus infinity
-- statement:
--   For the exact spectrally negative bounded-variation input of Theorem 4.10, with positive drift coefficient and jump traffic ratio greater than one, the input process tends to minus infinity almost surely. This is the stochastic drift step: apply the strong law to truncated integrable nonnegative loss increments, choose a truncation with mean exceeding the drift coefficient, and use monotonicity of the cumulative losses between integer times.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10, p. 100; auxiliary drift implication for stationaryWorkload_transientHighTraffic.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.overloadedInput_tendsto_atBot
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (hRho : 1 < (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift) :
    ∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => L.X t omega) atTop atBot := by
  sorry
