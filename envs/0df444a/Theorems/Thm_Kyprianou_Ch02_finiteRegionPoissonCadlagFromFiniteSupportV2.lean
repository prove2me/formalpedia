-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonCadlagFromFiniteSupportV2
-- name    : Kyprianou.Ch02.finiteRegionPoissonCadlagFromFiniteSupportV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T09:23:19.923053+00:00
-- url     : https://prove2.me/theorems/805711a8-430a-4fe5-8eed-4ff947ba6151
-- title:
--   Lemma 2.8 càdlàg gluing from all-window finite atomic support
-- statement:
--   The original KLS finite-region raw marked Poisson integral has càdlàg paths almost surely, provided a single full-measure event has finite point support on every integer-bounded window. On each compact time interval the measure is a finite atomic sum and the integral path a finite sum of right-continuous jump steps; locality then proves global càdlàg. The finite-support premise is a separately provable exact PRM consequence.
-- source:
--   Kyprianou Lemma 2.8, source LeanLevy/Processes/Cadlag.lean and LevyStochCalc Poisson/Atomic.lean + JumpSum.lean.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem finiteRegionPoissonCadlagFromFiniteSupportV2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hSupport : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      N.N ω ((Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) \ (s : Set (ℝ × ℝ))) = 0) :
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
      (fun t : ℝ≥0 => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) := by sorry
end Kyprianou.Ch02
