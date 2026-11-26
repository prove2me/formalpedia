-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteWindowWeightedL2V1
-- name    : Kyprianou.Ch04.finiteWindowWeightedL2V1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:48:59.475029+00:00
-- url     : https://prove2.me/theorems/edcd3d09-1710-4532-86cc-c80c2549bfd7
-- title:
--   Square integrability of measurable bounded compensated finite-window integrals
-- statement:
--   Square integrability of measurable bounded compensated finite-window integrals
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteWindowWeightedL2V1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfin : ν B < ⊤) (T : NNReal)
    (K : ℝ) (hK : 0 ≤ K) (g : ℝ → ℝ → Ω → ℝ)
    (hg : ∀ s x ω, 0 ≤ s → x ∈ B → |g s x ω| ≤ K)
    (M : Ω → ℝ) (hM : AEStronglyMeasurable M P)
    (hrep : ∀ ω, M ω =
      (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ B, g z.1 z.2 ω ∂(N.N ω)) -
      ∫ s in Icc (0 : ℝ) (T : ℝ), (∫ x in B, g s x ω ∂ν) ∂volume) :
    MemLp M 2 P := by
  sorry
end Kyprianou.Ch04
