-- Prove2me | Theorems.Thm_OAI_Problem356_PartitionTransport_exists_map_eq_sum_of_partition
-- name    : OAI.Problem356.PartitionTransport.exists_map_eq_sum_of_partition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:53:28.164985+00:00
-- url     : https://prove2.me/theorems/9c2b1fce-4809-4f74-a69b-3640ceaf94ad
-- title:
--   Gluing transports along a countable partition
-- statement:
--   Let $\mu$ be a measure, $(B_i)_{i\in\iota}$ a countable family of pairwise disjoint measurable sets covering $\mu$-almost everything, and $T_i$ measurable maps. Then there is a measurable $f$ with $f=T_i$ on $B_i$ and
--   $$
--   f_\#\mu=\sum_iT_{i\#}\bigl(\mu|_{B_i}\bigr) .
--   $$
--
--   Transports constructed cell by cell can be glued into a single measurable map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/PartitionTransport.lean#L16-L43

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure

open OAI OAI.Problem356
universe uAlpha uBeta uIndex uKappa
open MeasureTheory Set
open scoped ENNReal
variable {α : Type uAlpha} {β : Type uBeta} {ι : Type uIndex} [MeasurableSpace α] [MeasurableSpace β]

theorem OAI.Problem356.PartitionTransport.exists_map_eq_sum_of_partition [Countable ι] [Nonempty ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T : ι → α → β) (hT : ∀ i, Measurable (T i)) :
    ∃ f : α → β, Measurable f ∧
      (∀ i, EqOn f (T i) (B i)) ∧
      Measure.map f μ = Measure.sum (fun i => Measure.map (T i) (μ.restrict (B i))) := by sorry
