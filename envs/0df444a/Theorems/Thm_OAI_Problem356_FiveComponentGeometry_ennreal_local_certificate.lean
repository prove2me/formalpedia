-- Prove2me | Theorems.Thm_OAI_Problem356_FiveComponentGeometry_ennreal_local_certificate
-- name    : OAI.Problem356.FiveComponentGeometry.ennreal_local_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:46:08.926626+00:00
-- url     : https://prove2.me/theorems/c8b107a8-0fc3-438d-8ceb-08a460f74667
-- title:
--   The local certificate in extended-real form
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. Let $C$ be local supporting charts of the local Coulomb problem at an axis point $a$, with value function $V$, parameter radius $r$ and state radius $R$. For $y\in B(a,r)$, $x\in B(0,R)$ and $z\in B(-a,R)$ with $x,y,z$ pairwise distinct,
--   $$
--   \Bigl(\tfrac52-10|x|^2\Bigr)+V(y)+\Bigl(\tfrac54\langle a,z+a\rangle-10|z+a|^2\Bigr)\le c(x,y,z),
--   $$
--   with equality iff $x=\mathrm{central}(y)$ and $z=\mathrm{opposite}(y)$.
--
--   On collision-free triples the real supporting inequality has the same meaning for the extended-valued Coulomb cost.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/FiveComponentGeometry.lean#L121-L148

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

theorem OAI.Problem356.FiveComponentGeometry.ennreal_local_certificate {a : E3} (C : ChartsAt a) {x y z : E3}
    (hy : y ∈ ball a C.parameterRadius)
    (hx : x ∈ ball (0 : E3) C.stateRadius)
    (hz : z ∈ ball (-a) C.stateRadius)
    (hxy : 0 < dist x y) (hxz : 0 < dist x z) (hyz : 0 < dist y z) :
    ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2)) ≤ coulombCost (x, (y, z)) ∧
    (ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2)) = coulombCost (x, (y, z)) ↔
      x = C.charts.central y ∧ z = C.charts.opposite y) := by sorry
