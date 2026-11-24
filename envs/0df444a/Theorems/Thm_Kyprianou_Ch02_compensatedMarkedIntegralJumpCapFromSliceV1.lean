-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedMarkedIntegralJumpCapFromSliceV1
-- name    : Kyprianou.Ch02.compensatedMarkedIntegralJumpCapFromSliceV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:51:58.379939+00:00
-- url     : https://prove2.me/theorems/f0883c3a-1385-4c59-a760-14ec6ab86f4b
-- title:
--   A bounded marked measure integral has left jump bounded by the slice mass and common mark cap
-- statement:
--   A bounded marked measure integral has left jump bounded by the slice mass and common mark cap
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1

import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem compensatedMarkedIntegralJumpCapFromSliceV1
    (μ : Measure (ℝ × ℝ)) (A : Set ℝ) (hA : MeasurableSet A)
    (hsmall : ∀ x ∈ A, |x| < 1)
    (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (hfin : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ A) < ⊤)
    (c k : ℝ) (hc : 0 ≤ c)
    (hcut : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
      {x : ℝ | c < |x| ∧ |x| < 1}) = 0)
    (hslice : μ ({(t : ℝ)} ×ˢ A) ≤ 1) :
    ∃ l : ℝ,
      Tendsto (fun s : ℝ≥0 =>
        (∫ z in (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ A), z.2 ∂μ) - (s : ℝ) * k)
        (nhdsWithin t (Set.Iio t)) (nhds l) ∧
      |(∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A), z.2 ∂μ) -
        (t : ℝ) * k - l| ≤ c := by sorry
end Kyprianou.Ch02
