-- Prove2me | Theorems.Thm_OAI_Problem356_FiveComponentGeometry_fullConclusion_of_five_component_certificate
-- name    : OAI.Problem356.FiveComponentGeometry.fullConclusion_of_five_component_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:54:14.956046+00:00
-- url     : https://prove2.me/theorems/b8083b5f-c9c0-4161-8127-e5e8d9ae8fb5
-- title:
--   The five-component certificate yields the full conclusion
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. The five centers are $P_0=0$, $P_1=e_0$, $P_2=-e_0$, $P_3=e_1$, $P_4=-e_1$, where $e_0=(1,0,0)$ and $e_1=(0,1,0)$. Let $C_1,C_2$ be local supporting charts of the local Coulomb problem at $P_1$ and $P_3$, with value functions $V_1,V_2$. The five potentials are $v_0(x)=\frac52-10|x|^2$, $v_1=V_1$, $v_2(z)=\frac54\langle P_1,z+P_1\rangle-10|z+P_1|^2$, $v_3=V_2$ and $v_4(z)=\frac54\langle P_3,z+P_3\rangle-10|z+P_3|^2$. A triple is a branch contact if it is a permutation of $(\mathrm{central}(y),y,\mathrm{opposite}(y))$ for a chart parameter $y$ of $C_1$ or $C_2$. Assume the chart parameters and opposite points of $C_1,C_2$ stay outside $B(0,\frac14)$, and let $R>0$ be such that the balls $B(P_i,R)$ are pairwise disjoint. Let $u$ be measurable with $|u|\le M$, equal to $v_i$ on $B(P_i,R)$, such that on the union of these balls
--   $$
--   u(x)+u(y)+u(z)\le c(x,y,z),
--   $$
--   with equality only on branch contacts. Then some density has the full Coulomb conclusion.
--
--   A density $\rho$ has the full Coulomb conclusion if it is a smooth compact probability density whose measure $\mu=\rho\,dx$ has finite, attained Kantorovich value, admits no Monge optimizer, has Monge value equal to the Kantorovich value, and is approximated within any $\varepsilon>0$ by pairs of $\mu$-preserving maps of finite graph cost.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/ActualGeometryConclusion.lean#L33-L184

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
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterAxis

open OAI OAI.Problem356 OAI.Problem356.FiveComponentGeometry
open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace
open LocalGeometry CenterCertificate

theorem OAI.Problem356.FiveComponentGeometry.fullConclusion_of_five_component_certificate
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    (hout₁ : ∀ s ∈ C₁.charts.central.source,
      s ∉ ball (0 : E3) (1 / 4) ∧ C₁.charts.opposite s ∉ ball (0 : E3) (1 / 4))
    (hout₂ : ∀ s ∈ C₂.charts.central.source,
      s ∉ ball (0 : E3) (1 / 4) ∧ C₂.charts.opposite s ∉ ball (0 : E3) (1 / 4))
    {R : ℝ} (hR : 0 < R)
    (hdisj : Pairwise (fun i j : Fin 5 => Disjoint (ball (point i) R) (ball (point j) R)))
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x, |u x| ≤ M)
    (hueq : ∀ i x, x ∈ ball (point i) R → u x = potentials C₁ C₂ i x)
    (hcert : ∀ x ∈ ⋃ i : Fin 5, ball (point i) R,
      ∀ y ∈ ⋃ i : Fin 5, ball (point i) R, ∀ z ∈ ⋃ i : Fin 5, ball (point i) R,
      ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
      (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
        branchContact C₁ C₂ (x, (y, z)))) :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by sorry
