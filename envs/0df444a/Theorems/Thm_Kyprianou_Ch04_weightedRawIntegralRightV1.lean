-- Prove2me | Theorems.Thm_Kyprianou_Ch04_weightedRawIntegralRightV1
-- name    : Kyprianou.Ch04.weightedRawIntegralRightV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:34:09.617934+00:00
-- url     : https://prove2.me/theorems/65c11c3b-3eb9-5142-8b18-e5dc6345b379
-- title:
--   Right continuity of closed-window weighted Poisson integrals
-- statement:
--   Right continuity of closed-window weighted Poisson integrals
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem weightedRawIntegralRightV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : ℝ × ℝ → Ω → ℝ)
    (hz : ∀ᵐ ω ∂P, N.N ω (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0) :
    ∀ᵐ ω ∂P, ∀ t : NNReal,
      Tendsto (fun s : NNReal =>
        ∫ z in Icc (0 : ℝ) (s : ℝ) ×ˢ B, g z ω ∂(N.N ω))
        (𝓝[>] t) (𝓝 (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ B, g z ω ∂(N.N ω))) := by
  sorry
end Kyprianou.Ch04
