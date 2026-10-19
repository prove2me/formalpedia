-- Prove2me | Theorems.Thm_OAI_Problem356_LocalGeometry_LocalSupportingCharts_exists_shrink
-- name    : OAI.Problem356.LocalGeometry.LocalSupportingCharts.exists_shrink
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:19:36.28282+00:00
-- url     : https://prove2.me/theorems/57c88a12-4588-40b0-9d9f-c777b5ee0149
-- title:
--   Shrinking local supporting charts
-- statement:
--   Let $C$ be local supporting charts for $(F,G)$ at $(p,s)$, and $r_p,r_s>0$. Then there are local supporting charts $D$ at $(p,s)$ with
--   $$
--   \mathrm{source}(D)\subseteq\mathrm{source}(C)\cap B(p,r_p),\qquad\mathrm{state}(D)\subseteq\mathrm{state}(C)\cap B(s,r_s),
--   $$
--   and the same branch functions and value function as $C$.
--
--   The certificate survives arbitrary further restrictions. Values already computed at the centers are preserved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/LocalCertificate.lean#L145-L201

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

open OAI OAI.Problem356 OAI.Problem356.LocalGeometry
universe uE
open Set Filter
open scoped Topology ContDiff
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem OAI.Problem356.LocalGeometry.LocalSupportingCharts.exists_shrink [CompleteSpace E]
    {F : E × (E × E) → ℝ} {G : E × (E × E) → E × E} {p : E} {s : E × E}
    (C : LocalSupportingCharts F G p s) (rp rs : ℝ) (hp : 0 < rp) (hs : 0 < rs) :
    ∃ D : LocalSupportingCharts F G p s,
      D.charts.central.source ⊆ C.charts.central.source ∩ Metric.ball p rp ∧
      D.charts.stateDomain ⊆ C.charts.stateDomain ∩ Metric.ball s rs ∧
      (D.charts.central : E → E) = C.charts.central ∧
      (D.charts.opposite : E → E) = C.charts.opposite ∧ D.value = C.value := by sorry
