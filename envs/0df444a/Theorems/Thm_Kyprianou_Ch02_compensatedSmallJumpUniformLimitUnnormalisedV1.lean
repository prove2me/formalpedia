-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpUniformLimitUnnormalisedV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpUniformLimitUnnormalisedV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:01:36.462789+00:00
-- url     : https://prove2.me/theorems/c4cc19dd-c7ce-45b4-99c4-4e8e0c5f37a7
-- title:
--   Theorem 2.10 stochastic core: almost-sure compact-uniform subsequential small-jump limit before initial normalisation
-- statement:
--   For an arbitrary real Levy measure and its Poisson random measure, construct a common random path M and, for each finite horizon T, a deterministic strictly decreasing sequence of positive jump cutoffs approaching zero such that the compensated finite jump bands converge almost surely to M uniformly on that horizon. No value for M at time zero is prescribed. This is the substantive Doob inequality, L2 Cauchy subsequence and diagonal compact-horizon convergence obligation in Kyprianou Chapter 2 Theorem 2.10. The Chapter 2 parent normalises the path at zero by a separate proved finite-band identity.
-- source:
--   Kyprianou (2006), Theorem 2.10 small-jump stochastic uniform convergence core

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.compensatedSmallJumpUniformLimitUnnormalisedV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure) :
    ∃ (M : ℝ≥0 → Ω → ℝ),
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ)
    := by sorry
