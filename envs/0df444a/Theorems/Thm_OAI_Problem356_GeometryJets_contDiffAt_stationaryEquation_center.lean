-- Prove2me | Theorems.Thm_OAI_Problem356_GeometryJets_contDiffAt_stationaryEquation_center
-- name    : OAI.Problem356.GeometryJets.contDiffAt_stationaryEquation_center
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:08:04.506729+00:00
-- url     : https://prove2.me/theorems/9f730648-b83a-47d1-a00f-11e6b0a922e2
-- title:
--   Smoothness of the stationarity map at the reference point
-- statement:
--   Let $\phi(x)=|x|^{-1}$ on a real inner product space $E$, $K\in\mathbb{R}$ and $|a|=1$. The stationarity map of the regularized local problem is $G(p,(z,w))=\bigl(\nabla\phi(z-p)+\nabla\phi(z-w)+Kz,\ -\nabla\phi(z-w)-\nabla\phi(p-w)-\frac54a+K(w+a)\bigr)$, with reference point $(p,(z,w))=(a,(0,-a))$. Then for every order $n$ (including analytic),
--   $$
--   G\text{ is }C^n\text{ at }(a,(0,-a)) .
--   $$
--
--   At the reference point all pair separations $z-p=-a$, $z-w=a$ and $p-w=2a$ are nonzero. So the Coulomb gradients are analytic there.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/StationaryEquation.lean#L113-L127

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

open OAI OAI.Problem356 OAI.Problem356.GeometryJets
universe uE
open CoulombCalculus
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem OAI.Problem356.GeometryJets.contDiffAt_stationaryEquation_center {n : WithTop ENat}
    (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    ContDiffAt ℝ n (stationaryEquation K a) (a, (0, -a)) := by sorry
