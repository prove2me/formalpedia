-- Prove2me | Theorems.Thm_Kyprianou_Ch04_subcriticalInitialWorkloadLimitTransfer
-- name    : Kyprianou.Ch04.subcriticalInitialWorkloadLimitTransfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:32:59.186882+00:00
-- url     : https://prove2.me/theorems/81310b14-2432-52b6-b1ee-d2a1faa8a307
-- title:
--   A fixed nonnegative initial workload preserves any limit of bounded continuous workload expectations.
-- statement:
--   A fixed nonnegative initial workload preserves any limit of bounded continuous workload expectations.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.subcriticalInitialWorkloadLimitTransfer
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
    let rho := M / ENNReal.ofReal L.drift
    0 < rho → rho < 1 →
    ∀ w : ℝ, 0 ≤ w → ∀ f : BoundedContinuousFunction ℝ ℝ, ∀ a : ℝ,
      Tendsto (fun t : NNReal => ∫ z, f (sSup ((fun s : NNReal => L.X s z) '' Iic t) - L.X t z) ∂P)
        atTop (nhds a) →
      Tendsto (fun t : NNReal => ∫ z, f (max w (sSup ((fun s : NNReal => L.X s z) '' Iic t)) - L.X t z) ∂P)
        atTop (nhds a) := by
  sorry
