-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulSmallJumpCharFunFixedTimeLimitV1
-- name    : Kyprianou.Ch02.sourceFaithfulSmallJumpCharFunFixedTimeLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:15:22.011867+00:00
-- url     : https://prove2.me/theorems/65289e70-f57c-4768-9725-fc306c71b4f7
-- title:
--   Characteristic functions converge under the fixed-time small-jump approximation
-- statement:
--   Use fixed-time almost-everywhere convergence, measurability or measurable modifications of the band values and limit, and bounded convergence for characteristic functions.
-- source:
--   Kyprianou (2006), Chapter 2, proof of Theorem 2.1, compensated small-jump characteristic exponent

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
theorem sourceFaithfulSmallJumpCharFunFixedTimeLimitV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ) (hM : ProbabilityTheory.IsLevyProcess M P)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (t : ℝ≥0) (ξ : ℝ)
    (hlim : ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀,
        |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω - M t ω| < δ) :
    Tendsto (fun n => charFun
      (P.map (Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t)) ξ)
      atTop (nhds (charFun (P.map (M t)) ξ)) := by sorry
end Kyprianou.Ch02
