-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedUniformLimitIndependenceFromBandsV1
-- name    : Kyprianou.Ch02.compensatedUniformLimitIndependenceFromBandsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:58:22.796272+00:00
-- url     : https://prove2.me/theorems/cfaf63bc-77cd-4da2-ac24-59718849a576
-- title:
--   Joint independent increments inherited by the common small-jump uniform limit
-- statement:
--   For any finite monotone time partition, the vector of increments of the compensated finite-cutoff Poisson process converges almost surely to that of the common uniform limit. Joint independence is preserved under weak convergence of each coordinate and of the joint law; deduce Mathlib's iIndepFun property on every partition.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, Lévy independent increments

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem compensatedUniformLimitIndependenceFromBandsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ)
    (hzero : M 0 = fun _ => 0)
    (huniform :
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ))
    (hbands : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ProbabilityTheory.HasIndependentIncrements
        (Kyprianou.compensatedSmallJumpBand P levyMeasure N ε) P) :
    ProbabilityTheory.HasIndependentIncrements M P
    := by sorry
end Kyprianou.Ch02
