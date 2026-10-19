-- Prove2me | Theorems.Thm_OAI_Problem356_SmoothBranchMarginal_exists_smoothBranchData_of_smooth_charts
-- name    : OAI.Problem356.SmoothBranchMarginal.exists_smoothBranchData_of_smooth_charts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:39:37.366421+00:00
-- url     : https://prove2.me/theorems/97e29a92-ab81-4949-92b3-79ebd2caf513
-- title:
--   Smooth branch data from smooth local charts
-- statement:
--   Let $B=B(c,r)$ and let $e_0,\dots,e_3$ be local homeomorphisms of $\mathbb{R}^3$ that are smooth with smooth inverses, with $B$ in each source and $B,e_0(B),\dots,e_3(B)$ pairwise disjoint. Then there are smooth branch data on $B$ whose branches agree with the $e_i$ on $B$:
--   $$
--   H_i(x)=e_i(x)\qquad(x\in B) .
--   $$
--
--   These data provide a smooth compact density, a central probability carried by a compact core, measurable injective branches continuous on the core, disjoint components, and the mixture identity. Everything the measure-level arguments need is packaged here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/SmoothBranchMarginal.lean#L271-L318

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
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal

open OAI OAI.Problem356 OAI.Problem356.SmoothBranchMarginal
open MeasureTheory Set
open scoped ENNReal

theorem OAI.Problem356.SmoothBranchMarginal.exists_smoothBranchData_of_smooth_charts
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (componentRegion (Metric.ball c r) e i) (componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source)
    (he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target) :
    ∃ d : SmoothBranchData (Metric.ball c r),
      ∀ i x, x ∈ Metric.ball c r → d.branch i x = e i x := by sorry
