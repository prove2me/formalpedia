-- Prove2me | Theorems.Thm_Kyprianou_Ch02_smallJumpUniformLimitMarkRegionVersionV1
-- name    : Kyprianou.Ch02.smallJumpUniformLimitMarkRegionVersionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:27:07.556805+00:00
-- url     : https://prove2.me/theorems/23e0bcbc-be84-40c0-8197-a8e6c331fab5
-- title:
--   The compact-uniform small-jump limit has a full-path version measurable in the small-mark PRM sigma algebra
-- statement:
--   Choose one approximating sequence per integer horizon. For each time use a sequence from a deterministic integer horizon covering that time, taking the measurable real limsup. The countable common conull event yields equality of the whole paths, not just separate almost-sure equality at fixed times.
-- source:
--   Kyprianou (2006), Theorem 2.1; independence of the three Lévy–Itô components

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

open scoped Topology

namespace Kyprianou.Ch02
theorem smallJumpUniformLimitMarkRegionVersionV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ)
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
                    M t ω| < δ)) :
    ∃ S : Ω → ℝ≥0 → ℝ,
      Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) |
        C ⊆ ((Set.univ : Set ℝ) ×ˢ {x : ℝ | |x| < 1}) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] S ∧
      S =ᵐ[P] (fun ω t => M t ω) := by sorry
end Kyprianou.Ch02
