-- Prove2me | Theorems.Thm_OAI_Problem356_strictConvexOn_of_positive_hessian
-- name    : OAI.Problem356.strictConvexOn_of_positive_hessian
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:14:08.148151+00:00
-- url     : https://prove2.me/theorems/f8893e93-4670-43b8-b98b-4e2d4112f08e
-- title:
--   Positive-definite Hessians give strict convexity
-- statement:
--   Let $s$ be an open convex set in a real normed space, and $f$ with derivative $f'(z)$ and second derivative $f''(z)$ at every $z\in s$. If
--   $$
--   f''(z)(v,v)>0\qquad\text{for all }z\in s,\ v\ne0,
--   $$
--   then $f$ is strictly convex on $s$.
--
--   The derivative fields are explicit, so this applies directly to computed Hessians.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/StrictMinimum.lean#L76-L105

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

open OAI OAI.Problem356
universe uE uP
open Set Filter
open scoped Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem OAI.Problem356.strictConvexOn_of_positive_hessian {s : Set E} {f : E → ℝ}
    {f' : E → E →L[ℝ] ℝ} {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hs : Convex ℝ s) (hsopen : IsOpen s)
    (hf : ∀ z ∈ s, HasFDerivAt f (f' z) z)
    (hf' : ∀ z ∈ s, HasFDerivAt f' (f'' z) z)
    (hpos : ∀ z ∈ s, ∀ v : E, v ≠ 0 → 0 < f'' z v v) :
    StrictConvexOn ℝ s f := by sorry
