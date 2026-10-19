-- Prove2me | Theorems.Thm_OAI_Problem356_StationaryMap_hasFDerivAt_statePotential
-- name    : OAI.Problem356.StationaryMap.hasFDerivAt_statePotential
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:20:46.083984+00:00
-- url     : https://prove2.me/theorems/3d9d3b95-2dbf-4150-8780-5f1825d4a4c9
-- title:
--   The stationary map is the state derivative of the local potential
-- statement:
--   Let $\phi(x)=|x|^{-1}$ on a real inner product space, $a$ a vector and $y$ a parameter. For a state $s=(s_1,s_2)$ with $s_1\ne y$, $s_1\ne s_2$, $s_2\ne y$, the state potential
--   $$
--   \phi(s_1-y)+\phi(s_1-s_2)+\phi(s_2-y)-\bigl(\tfrac52-10|s_1|^2\bigr)-\bigl(\tfrac54\langle a,s_2+a\rangle-10|s_2+a|^2\bigr)
--   $$
--   has derivative at $s$ equal to the linear form $(u,v)\mapsto\langle G_1,u\rangle+\langle G_2,v\rangle$, where $G=(G_1,G_2)$ is the stationary map.
--
--   So zeros of the stationary map are exactly the critical points of the local potential in the state.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/StationaryMap.lean#L84-L103

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

open OAI OAI.Problem356 OAI.Problem356.StationaryMap
universe uE
open scoped RealInnerProductSpace
open CoulombCalculus
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem OAI.Problem356.StationaryMap.hasFDerivAt_statePotential (a y : E) {s : E × E}
    (hxy : s.1 ≠ y) (hxz : s.1 ≠ s.2) (hzy : s.2 ≠ y) :
    HasFDerivAt (statePotential a y) (stateDifferential a y s) s := by sorry
