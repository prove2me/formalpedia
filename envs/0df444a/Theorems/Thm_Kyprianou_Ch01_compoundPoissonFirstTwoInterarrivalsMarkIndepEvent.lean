-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonFirstTwoInterarrivalsMarkIndepEvent
-- name    : Kyprianou.Ch01.compoundPoissonFirstTwoInterarrivalsMarkIndepEvent
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T12:48:48.880005+00:00
-- url     : https://prove2.me/theorems/32437b82-4dea-4ec2-a96d-ebb4ee3724cd
-- title:
--   Three independent source compound-Poisson variables factor the first two interarrival and first mark events
-- statement:
--   Under the exact source IsCompoundPoissonDriver, the first two real interarrival coordinates and first real mark are jointly independent. For any real thresholds u,v and real mark a, the probability of {τ0≤u, τ1≤v, mark0=a} equals the product of its marginal event probabilities. Prove using hdriver.indep.indepFun_prodMk for the pair (τ0,τ1) and mark0, hdriver.indep.indepFun for τ0 and τ1, and IndepFun.measure_inter_preimage_eq_mul. This is the finite-dimensional independence lemma needed for marked two-arrival probability factorisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonFirstTwoInterarrivalsMarkIndepEvent
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (u v a : ℝ) :
    Q {ω | arrival 0 ω ≤ u ∧ arrival 1 ω ≤ v ∧ marks 0 ω = a} =
      Q {ω | arrival 0 ω ≤ u} *
        Q {ω | arrival 1 ω ≤ v} *
        Q {ω | marks 0 ω = a} := by
  sorry
