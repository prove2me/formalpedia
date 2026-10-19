-- Prove2me | Theorems.Thm_OAI_Problem356_FiveComponentGeometry_exists_canonical_neighborhoods
-- name    : OAI.Problem356.FiveComponentGeometry.exists_canonical_neighborhoods
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:49:08.547904+00:00
-- url     : https://prove2.me/theorems/a5af7801-2b36-420f-b4a6-9f7de9f476d3
-- title:
--   Neighborhoods on which both canonical certificates hold
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. The five centers are $P_0=0$, $P_1=e_0$, $P_2=-e_0$, $P_3=e_1$, $P_4=-e_1$, where $e_0=(1,0,0)$ and $e_1=(0,1,0)$. Let $C_1,C_2$ be local supporting charts of the local Coulomb problem at $P_1$ and $P_3$, with value functions $V_1,V_2$. The five potentials are $v_0(x)=\frac52-10|x|^2$, $v_1=V_1$, $v_2(z)=\frac54\langle P_1,z+P_1\rangle-10|z+P_1|^2$, $v_3=V_2$ and $v_4(z)=\frac54\langle P_3,z+P_3\rangle-10|z+P_3|^2$. A triple is a branch contact if it is a permutation of $(\mathrm{central}(y),y,\mathrm{opposite}(y))$ for a chart parameter $y$ of $C_1$ or $C_2$. Then there are neighborhoods $W_i$ of $P_i$ ($i=0,\dots,4$) such that the local type certificates hold for the ordered types $(0,1,2)$ and $(0,3,4)$: for $x\in W_0$, $y\in W_j$, $z\in W_k$ with $(j,k)\in\{(1,2),(3,4)\}$,
--   $$
--   v_0(x)+v_j(y)+v_k(z)\le c(x,y,z),
--   $$
--   and equality forces a branch contact.
--
--   Both canonical orders are certified on one common family of component neighborhoods.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/FiveComponentCanonical.lean#L14-L91

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
open scoped ENNReal
open CenterCertificate GoodTypePermutation

theorem OAI.Problem356.FiveComponentGeometry.exists_canonical_neighborhoods
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∃ W : Fin 5 → Set E3,
      (∀ i, W i ∈ nhds (point i)) ∧
      LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 1 2 ∧
      LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 3 4 := by sorry
