-- Prove2me | Theorems.Thm_Kyprianou_Ch02_smallJumpPathRegionalMeasurableVersionV1
-- name    : Kyprianou.Ch02.smallJumpPathRegionalMeasurableVersionV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:35:33.453576+00:00
-- url     : https://prove2.me/theorems/8902690e-17c9-46ee-b7e3-af090f9888af
-- title:
--   Small-jump path has a regional-measurable coordinatewise version
-- statement:
--   A compact-uniform compensated small-jump approximation gives a small-mark regional-measurable path with almost surely equal coordinates.
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
theorem smallJumpPathRegionalMeasurableVersionV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ)
    (hM : ProbabilityTheory.IsLevyProcess M P)
    (huniform :
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ))
 :
    ∃ S : Ω → ℝ≥0 → ℝ,
      Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) |
        C ⊆ ((Set.univ : Set ℝ) ×ˢ {x : ℝ | |x| < 1}) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] S ∧
      ∀ t, (fun ω => S ω t) =ᵐ[P] M t := by sorry
end Kyprianou.Ch02
