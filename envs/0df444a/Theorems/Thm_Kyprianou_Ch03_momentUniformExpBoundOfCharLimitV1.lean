-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentUniformExpBoundOfCharLimitV1
-- name    : Kyprianou.Ch03.momentUniformExpBoundOfCharLimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:35:17.615802+00:00
-- url     : https://prove2.me/theorems/97c5a9b3-1dc8-4789-a0f1-5b6b7cbf96d6
-- title:
--   Uniform exponential moment bounds pass to a characteristic-function limit
-- statement:
--   Use the proved Lévy continuity theorem to obtain weak convergence. Apply it to bounded continuous truncations of the positive exponential, pass the bound to the limit, and take the increasing supremum of truncation levels via monotone convergence.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8: finite compound-Poisson law and exponential moment of the compensated small-jump law.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentUniformExpBoundOfCharLimitV1
    (q : ℕ → ProbabilityMeasure Real) (nu : ProbabilityMeasure Real)
    (hchar : ∀ xi : Real, Tendsto (fun n => charFun (q n : Measure Real) xi) atTop
      (𝓝 (charFun (nu : Measure Real) xi)))
    (b : Real) (C : ENNReal) (hC : C < ⊤)
    (hbound : ∀ n, (∫⁻ x, ENNReal.ofReal (Real.exp (b * x)) ∂(q n : Measure Real)) ≤ C) :
    Integrable (fun x : Real => Real.exp (b * x)) (nu : Measure Real) := by sorry
