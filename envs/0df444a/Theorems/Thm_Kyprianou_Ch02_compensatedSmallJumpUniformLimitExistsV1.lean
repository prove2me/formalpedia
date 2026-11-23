-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpUniformLimitExistsV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpUniformLimitExistsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:42:18.354391+00:00
-- url     : https://prove2.me/theorems/84ff5197-053b-4e8a-be0f-af231b037803
-- title:
--   Theorem 2.10: common small-jump limit and uniform compact-horizon subsequences
-- statement:
--   Construct a version M with M(0)=0 pointwise and uniformly almost-sure finite-horizon deterministic truncation subsequences. Establish the limit from Lévy measure square integrability, compensated Poisson isometry, Doob maximal control and a summable-subsequence Borel-Cantelli argument.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, stochastic construction

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
theorem compensatedSmallJumpUniformLimitExistsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure) :
    ∃ (M : ℝ≥0 → Ω → ℝ),
      (M 0 = fun _ => 0) ∧
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ)
    := by sorry
end Kyprianou.Ch02
