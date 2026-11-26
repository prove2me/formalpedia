-- Prove2me | Theorems.Thm_MultiPeriod_measurableSet_feasGraph_fiber_hit
-- name    : MultiPeriod.measurableSet_feasGraph_fiber_hit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:35.806629+00:00
-- url     : https://prove2.me/theorems/b86e5840-0f5a-446e-81e5-1518079eae11
-- title:
--   Multi Period: measurable Set feas Graph fiber hit
-- statement:
--   The constrained-fiber hit-set against a closed target is Borel:
--       transport the closed couplings hit-set (U4) along the continuous
--       marginal map of the Feller model.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L325-L364
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LscBellman.lean#L325-L364

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
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
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)

theorem MultiPeriod.measurableSet_feasGraph_fiber_hit
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t)) (t : ℕ)
    {C : Set (WeakP (X (t + 1) × Y (t + 1)))} (hC : IsClosed C) :
    MeasurableSet {h : PairHist X Y t |
      ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C).Nonempty} := by sorry
