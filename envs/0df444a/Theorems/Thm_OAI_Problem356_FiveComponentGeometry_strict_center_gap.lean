-- Prove2me | Theorems.Thm_OAI_Problem356_FiveComponentGeometry_strict_center_gap
-- name    : OAI.Problem356.FiveComponentGeometry.strict_center_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:43:41.39223+00:00
-- url     : https://prove2.me/theorems/0e2f03bf-9c33-4c62-bd49-cd695eedb0ae
-- title:
--   The actual potentials have strict gaps at bad center types
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. The five centers are $P_0=0$, $P_1=e_0$, $P_2=-e_0$, $P_3=e_1$, $P_4=-e_1$, where $e_0=(1,0,0)$ and $e_1=(0,1,0)$. Let $C_1,C_2$ be local supporting charts of the local Coulomb problem at $P_1$ and $P_3$, with value functions $V_1,V_2$. The five potentials are $v_0(x)=\frac52-10|x|^2$, $v_1=V_1$, $v_2(z)=\frac54\langle P_1,z+P_1\rangle-10|z+P_1|^2$, $v_3=V_2$ and $v_4(z)=\frac54\langle P_3,z+P_3\rangle-10|z+P_3|^2$. A triple is a branch contact if it is a permutation of $(\mathrm{central}(y),y,\mathrm{opposite}(y))$ for a chart parameter $y$ of $C_1$ or $C_2$. If an ordered index triple $(i,j,k)$ is not good, i.e. $\{i,j,k\}\notin\{\{0,1,2\},\{0,3,4\}\}$, then
--   $$
--   v_i(P_i)+v_j(P_j)+v_k(P_k)<c(P_i,P_j,P_k) .
--   $$
--
--   At the centers the five potentials take exactly the values of the finite center certificate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/FiveComponentGeometry.lean#L100-L119

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
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry

open OAI OAI.Problem356 OAI.Problem356.FiveComponentGeometry
open Set Filter Metric
open scoped ENNReal InnerProductSpace
open LocalGeometry StationaryMap CenterCertificate

theorem OAI.Problem356.FiveComponentGeometry.strict_center_gap (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (i j k : Fin 5) (h : ¬ Good i j k) :
    ENNReal.ofReal (potentials C₁ C₂ i (point i) +
      potentials C₁ C₂ j (point j) + potentials C₁ C₂ k (point k)) <
      coulombCost (point i, (point j, point k)) := by sorry
