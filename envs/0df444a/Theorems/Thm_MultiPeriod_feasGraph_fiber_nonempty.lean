-- Prove2me | Theorems.Thm_MultiPeriod_feasGraph_fiber_nonempty
-- name    : MultiPeriod.feasGraph_fiber_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:52.613805+00:00
-- url     : https://prove2.me/theorems/408b3d52-98ed-4537-8a72-f50af91500f2
-- title:
--   Multi Period: feas Graph fiber nonempty
-- statement:
--   Fibers of the feasibility graph are nonempty when the one-step
--       feasible sets are: feasible plans of probability marginals are
--       probability measures (L0).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableStrategy.lean#L44-L53
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableStrategy.lean#L44-L53

import Definitions.Def_BicausalOT_SemianalyticValue
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
import Definitions.Def_BicausalOT_MeasurableStrategy
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)]

theorem MultiPeriod.feasGraph_fiber_nonempty
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty)
    (t : ℕ) (h : PairHist X Y t) :
    ∃ γ : WeakP (X (t + 1) × Y (t + 1)), (h, γ) ∈ FeasGraph κμ κν t := by sorry
