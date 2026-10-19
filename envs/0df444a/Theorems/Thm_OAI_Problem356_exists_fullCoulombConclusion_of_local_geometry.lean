-- Prove2me | Theorems.Thm_OAI_Problem356_exists_fullCoulombConclusion_of_local_geometry
-- name    : OAI.Problem356.exists_fullCoulombConclusion_of_local_geometry
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:40:27.987232+00:00
-- url     : https://prove2.me/theorems/f4bd3e87-a250-46a9-a50a-9b3f91407e38
-- title:
--   Local branch geometry with a supporting potential yields the full conclusion
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. Let $B=B(c,r)$ and let $e_0,\dots,e_3$ be smooth local homeomorphisms with smooth inverses, $B$ in each source, and $B,e_0(B),\dots,e_3(B)$ pairwise disjoint and contained in a measurable set $U$. Let $u$ be measurable with $|u|\le M$ on $U$ such that:
--
--   1. on $U^3$,
--   $$
--   u(x)+u(y)+u(z)\le c(x,y,z) ;
--   $$
--   2. equality holds at $(x,e_0x,e_1x)$ and $(x,e_2x,e_3x)$ for all $x\in B$;
--   3. equality with $x\in B$ and $y,z\in U$ forces $y=e_ix$ for some $i$.
--
--   Then some smooth compact probability density $\rho$ has the full Coulomb conclusion. Its Kantorovich value is finite and attained, no Monge optimizer exists, the Monge value equals the Kantorovich value, and it is approximated by measure-preserving maps of finite cost.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/ExistenceFromLocalGeometry.lean#L15-L98

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

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal

theorem OAI.Problem356.exists_fullCoulombConclusion_of_local_geometry
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (SmoothBranchMarginal.componentRegion (Metric.ball c r) e i)
      (SmoothBranchMarginal.componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source)
    (he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target)
    {U : Set E3} (hU : MeasurableSet U)
    (hBU : Metric.ball c r ⊆ U) (heU : ∀ i, e i '' Metric.ball c r ⊆ U)
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x ∈ U, -M ≤ u x ∧ u x ≤ M)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
        coulombCost t)
    (hcontact01 : ∀ x ∈ Metric.ball c r,
      ENNReal.ofReal (u x + u (e 0 x) + u (e 1 x)) = coulombCost (x, (e 0 x, e 1 x)))
    (hcontact23 : ∀ x ∈ Metric.ball c r,
      ENNReal.ofReal (u x + u (e 2 x) + u (e 3 x)) = coulombCost (x, (e 2 x, e 3 x)))
    (hselect : ∀ x y z : E3, x ∈ Metric.ball c r → y ∈ U → z ∈ U →
      ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
      ∃ i, y = e i x) :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by sorry
