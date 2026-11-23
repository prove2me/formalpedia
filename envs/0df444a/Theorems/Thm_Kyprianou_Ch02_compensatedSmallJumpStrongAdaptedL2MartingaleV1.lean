-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpStrongAdaptedL2MartingaleV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpStrongAdaptedL2MartingaleV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:39:32.569332+00:00
-- url     : https://prove2.me/theorems/2a59f577-d160-4f14-9790-d9c87b3eade3
-- title:
--   Theorem 2.10: L² martingale transfer for a strongly adapted small-jump limit
-- statement:
--   Assuming the limit is strongly adapted, transfer the fixed-completed-filtration finite-band L² martingales through the Poisson second moment bound and almost-sure compact-uniform convergence, obtaining the martingale identity and timewise MemLp 2. The strong-adaptation hypothesis rules out the accepted counterexample to the old unconditional transfer.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, measurable martingale version correction

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
theorem compensatedSmallJumpStrongAdaptedL2MartingaleV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ)
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
    (hadapt : MeasureTheory.StronglyAdapted ℱ M)
    (hband : ∀ ε : ℝ, 0 < ε → ε < 1 →
      MeasureTheory.Martingale
        (Kyprianou.compensatedSmallJumpBand P levyMeasure N ε) ℱ P ∧
      ∀ t : ℝ≥0,
        MemLp (Kyprianou.compensatedSmallJumpBand P levyMeasure N ε t) 2 P) :
    MeasureTheory.Martingale M ℱ P ∧
    ∀ t : ℝ≥0, MemLp (M t) 2 P
    := by sorry
end Kyprianou.Ch02
