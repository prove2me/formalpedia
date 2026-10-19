-- Prove2me | Theorems.Thm_OAI_Problem356_convex_isMinOn_of_hasFDerivAt_zero
-- name    : OAI.Problem356.convex_isMinOn_of_hasFDerivAt_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:11:25.635982+00:00
-- url     : https://prove2.me/theorems/11e0f889-5707-430b-bf7c-ef6eccacf96b
-- title:
--   Stationary points of convex functions are minima
-- statement:
--   Let $f$ be convex on a set $s$ of a real normed space, $x\in s$, and suppose $f$ has derivative $0$ at $x$. Then
--   $$
--   f(x)\le f(y)\qquad\text{for all }y\in s .
--   $$
--
--   A critical point of a convex function is a global minimizer on its convexity domain.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/StrictMinimum.lean#L16-L31

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

theorem OAI.Problem356.convex_isMinOn_of_hasFDerivAt_zero {s : Set E} {f : E → ℝ} {x : E}
    (hf : ConvexOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) : IsMinOn f s x := by sorry
