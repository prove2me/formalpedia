-- Prove2me | Theorems.Thm_MultiPeriod_exists_measurable_feasible_strategy
-- name    : MultiPeriod.exists_measurable_feasible_strategy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:33:36.592842+00:00
-- url     : https://prove2.me/theorems/7aad9107-342e-5fdc-8ad3-1dad1544b935
-- title:
--   Multi Period: exists measurable feasible strategy
-- statement:
--   **Measurable feasible strategies exist (E3-D).** In the Borel model —
--       weak-Borel measurable probability kernels, no continuity and no cost
--       hypotheses — there is a strategy that is pointwise feasible and
--       plain-Borel measurable at every stage: measurable bicausal Markov
--       strategies exist.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableFeasibleStrategy.lean#L114-L137
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableFeasibleStrategy.lean#L114-L137

import Definitions.Def_BicausalOT_LscBellman
import Definitions.Def_BicausalOT_MeasurableFeasibleStrategy
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))

theorem MultiPeriod.exists_measurable_feasible_strategy
    (hκμ_measW : ∀ t, @Measurable (XHist X t) (WeakP (X (t + 1)))
      _ _ (κμP t))
    (hκν_measW : ∀ t, @Measurable (YHist Y t) (WeakP (Y (t + 1)))
      _ _ (κνP t)) :
    ∃ γfeas : Strat X Y,
      (∀ t h, γfeas t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        Measurable φ ∧ ∀ h, γfeas t h = (φ h).toMeasure) := by sorry
