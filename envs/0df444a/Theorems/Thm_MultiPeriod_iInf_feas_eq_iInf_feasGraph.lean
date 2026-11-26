-- Prove2me | Theorems.Thm_MultiPeriod_iInf_feas_eq_iInf_feasGraph
-- name    : MultiPeriod.iInf_feas_eq_iInf_feasGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:13.065922+00:00
-- url     : https://prove2.me/theorems/04bcc6fc-b1b5-59fe-b3cd-af5ba3992ba2
-- title:
--   Multi Period: i Inf feas eq i Inf feas Graph
-- statement:
--   The one-step feasible infimum reindexed over the fibers of the
--       feasibility graph (any integrand): legitimate because feasible
--       one-step plans are probability measures.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/SemianalyticValue.lean#L143-L158
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/SemianalyticValue.lean#L143-L158

import Definitions.Def_BicausalOT_MultiPeriodTopology
import Definitions.Def_BicausalOT_FeasNonempty
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_SemianalyticValue
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

theorem MultiPeriod.iInf_feas_eq_iInf_feasGraph
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (t : ℕ) (h : PairHist X Y t) (f : X (t + 1) × Y (t + 1) → ℝ≥0∞) :
    (⨅ (γm : Measure (X (t + 1) × Y (t + 1))) (_ : γm ∈ Feas κμ κν t h),
        ∫⁻ z, f z ∂γm)
      = ⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
          (_ : (h, γ) ∈ FeasGraph κμ κν t),
          ∫⁻ z, f z ∂γ.toMeasure := by sorry
