-- Prove2me | Theorems.Thm_MultiPeriod_measurableSet_feasGraph_fiber_hit_of_measurable
-- name    : MultiPeriod.measurableSet_feasGraph_fiber_hit_of_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:03.516223+00:00
-- url     : https://prove2.me/theorems/04c7d6a8-c408-4123-a18f-dcb75d8d1022
-- title:
--   Multi Period: measurable Set feas Graph fiber hit of measurable
-- statement:
--   Hit-sets of the feasibility fibers against open sets are Borel, for
--       weak-Borel measurable kernels: Fσ decomposition of the open set and
--       transport of the closed couplings hit-sets (U4) along the measurable
--       marginal-pair map.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableFeasibleStrategy.lean#L38-L107
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableFeasibleStrategy.lean#L38-L107

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

theorem MultiPeriod.measurableSet_feasGraph_fiber_hit_of_measurable
    (hκμ_measW : ∀ t, @Measurable (XHist X t) (WeakP (X (t + 1)))
      _ _ (κμP t))
    (hκν_measW : ∀ t, @Measurable (YHist Y t) (WeakP (Y (t + 1)))
      _ _ (κνP t)) (t : ℕ)
    {U : Set (WeakP (X (t + 1) × Y (t + 1)))} (hU : IsOpen U) :
    MeasurableSet {h : PairHist X Y t |
      ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ U).Nonempty} := by sorry
