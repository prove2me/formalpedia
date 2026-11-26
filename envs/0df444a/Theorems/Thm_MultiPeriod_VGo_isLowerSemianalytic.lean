-- Prove2me | Theorems.Thm_MultiPeriod_VGo_isLowerSemianalytic
-- name    : MultiPeriod.VGo_isLowerSemianalytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:31.869962+00:00
-- url     : https://prove2.me/theorems/1c7f2468-4829-533b-b046-79b81d0a6652
-- title:
--   Multi Period: VGo is Lower Semianalytic
-- statement:
--   **Phase 3 (BS Proposition 8.2 analogue).** For Borel Markov kernels
--       and lower semianalytic stage costs, every Bellman value function
--       `VGo k t` is lower semianalytic on the history space.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/SemianalyticValue.lean#L180-L214
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/SemianalyticValue.lean#L180-L214

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

theorem MultiPeriod.VGo_isLowerSemianalytic
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y))
    (hc : ∀ t, IsLowerSemianalytic (c t)) :
    ∀ k t : ℕ, IsLowerSemianalytic (VGo c κμ κν k t) := by sorry
