-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonIntegralLocalFiniteStepV1
-- name    : Kyprianou.Ch02.finiteRegionPoissonIntegralLocalFiniteStepV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T09:46:57.455594+00:00
-- url     : https://prove2.me/theorems/634eda78-5c0e-47d8-b44a-91d385e07662
-- title:
--   Local finite marked-step identity for KLS Poisson integral
-- statement:
--   The source-exact KLS raw marked Poisson integral has a finite marked-step representation on an open neighbourhood of each positive or zero time, on one common full-measure event, assuming the independently stated almost-sure finite support of the PRM on every natural bounded window. Choose a natural horizon above t and finite support s on (0,T]×B. As every smaller time window is contained in that region, the restricted measure can be represented by finitely many atoms; the weight at each point is its marked mass. The nontrivial integration-of-finite-atomic-measure, support-restriction and common-null-set reasoning remain to be proved.
-- source:
--   Kyprianou Chapter 2 Lemma 2.8; KLS Poisson/Atomic.lean, JumpSum.lean; LeanLevy Processes/Cadlag.lean bandJumpSum_eqOn_Iio.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem finiteRegionPoissonIntegralLocalFiniteStepV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hSupport : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      N.N ω ((Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) \ (s : Set (ℝ × ℝ))) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∃ T : ℝ≥0, t < T ∧
      ∃ (s : Finset (ℝ × ℝ)) (w : ℝ × ℝ → ℝ),
        ∀ u : ℝ≥0, u < T →
          (∫ z in (Set.Ioc (0 : ℝ) (u : ℝ) ×ˢ B),
            z.2 ∂(N.N ω)) =
            ∑ p ∈ s, if p.1 ≤ (u : ℝ) then w p else 0 := by sorry
end Kyprianou.Ch02
