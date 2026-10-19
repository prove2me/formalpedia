-- Prove2me | Theorems.Thm_OAI_Problem356_strictConvex_eq_iff_of_hasFDerivAt_zero
-- name    : OAI.Problem356.strictConvex_eq_iff_of_hasFDerivAt_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:12:09.847027+00:00
-- url     : https://prove2.me/theorems/0d35d671-485b-488b-9a85-59a9b9e0b74f
-- title:
--   Stationary points of strictly convex functions are unique minima
-- statement:
--   Let $f$ be strictly convex on $s$, $x\in s$ with derivative $0$ at $x$, and $y\in s$. Then
--   $$
--   f(y)=f(x)\iff y=x .
--   $$
--
--   Strict convexity of the local potential is what makes the contact set exactly the stationary branch.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/StrictMinimum.lean#L33-L48

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

theorem OAI.Problem356.strictConvex_eq_iff_of_hasFDerivAt_zero {s : Set E} {f : E → ℝ} {x : E}
    (hf : StrictConvexOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) {y : E} (hy : y ∈ s) :
    f y = f x ↔ y = x := by sorry
