-- Prove2me | Theorems.Thm_OAI_Problem356_CoulombSupportExistence_nonempty_coulombLocalSupportingCharts
-- name    : OAI.Problem356.CoulombSupportExistence.nonempty_coulombLocalSupportingCharts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:41:19.980961+00:00
-- url     : https://prove2.me/theorems/4807d7d8-fa36-4c20-85ab-7d7ef03cc39f
-- title:
--   The Coulomb branches carry exact local supporting potentials
-- statement:
--   For an axis $k$, consider the local potential $F(y,(s_1,s_2))$ (the Coulomb cost of $(s_1,y,s_2)$ minus the prescribed potentials at $s_1$ and $s_2$) and its stationarity map $G$ with $K=20$, at the reference point $(e_k,(0,-e_k))$. Then local supporting charts exist. For every outer point $y$ near $e_k$, the stationary branch point is the unique minimizer of $F(y,\cdot)$ near $(0,-e_k)$, with value
--   $$
--   V(y)=\min_{s}F(y,s)
--   $$
--   analytic in $y$.
--
--   The minimum value $V$ is the supporting potential at the moving outer point, and equality holds exactly on the branch.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CoulombSupportExistence.lean#L43-L99

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
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence

open OAI OAI.Problem356 OAI.Problem356.CoulombSupportExistence
open Filter Set
open scoped Topology ContDiff RealInnerProductSpace
open CoulombCalculus GeometryJets LocalGeometry

theorem OAI.Problem356.CoulombSupportExistence.nonempty_coulombLocalSupportingCharts (k : Fin 3) :
    Nonempty (LocalSupportingCharts
      (StationaryMap.jointPotential (axisVector k))
      (stationaryEquation 20 (axisVector k))
      (axisVector k) (0, -axisVector k)) := by sorry
