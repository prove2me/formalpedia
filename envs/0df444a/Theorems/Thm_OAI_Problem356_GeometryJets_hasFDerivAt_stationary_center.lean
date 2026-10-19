-- Prove2me | Theorems.Thm_OAI_Problem356_GeometryJets_hasFDerivAt_stationary_center
-- name    : OAI.Problem356.GeometryJets.hasFDerivAt_stationary_center
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:08:44.483878+00:00
-- url     : https://prove2.me/theorems/9c7e703a-e267-4e4e-b0b3-9757ab4a8370
-- title:
--   The derivative of the stationarity map at the center
-- statement:
--   Let $\phi(x)=|x|^{-1}$ on a real inner product space $E$, $K\in\mathbb{R}$ and $|a|=1$. The stationarity map of the regularized local problem is $G(p,(z,w))=\bigl(\nabla\phi(z-p)+\nabla\phi(z-w)+Kz,\ -\nabla\phi(z-w)-\nabla\phi(p-w)-\frac54a+K(w+a)\bigr)$, with reference point $(p,(z,w))=(a,(0,-a))$. Let $Q=D^2\phi(a)$ be the Hessian of $\phi$ at the unit vector $a$. Then the derivative of $G$ at $(a,(0,-a))$ is
--   $$
--   (v,(u_1,u_2))\mapsto\bigl(-Qv,-\tfrac18Qv\bigr)+\bigl((2Q+K)u_1-Qu_2,\ -Qu_1+(\tfrac98Q+K)u_2\bigr).
--   $$
--
--   The parameter block and the state block are explicit multiples of the single Hessian $Q$, using that $D^2\phi$ is even and scales like $|x|^{-3}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/StationaryEquation.lean#L135-L163

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

theorem OAI.Problem356.GeometryJets.hasFDerivAt_stationary_center (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt (stationaryEquation K a)
      (centerTotalDerivative K (pairHessian a)) (a, (0, -a)) := by sorry
