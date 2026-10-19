-- Prove2me | Theorems.Thm_OAI_Problem356_exists_glued_component_certificate
-- name    : OAI.Problem356.exists_glued_component_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:32:48.136584+00:00
-- url     : https://prove2.me/theorems/6cc580c2-6444-4123-a8a7-b8a239c2b277
-- title:
--   A glued supporting potential on small disjoint component balls
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. Let $p_i$ ($i$ finite) be distinct centers, $V_i\ni p_i$ open, and $v_i$ continuous on $V_i$. Let $\mathrm{Good}$ be a predicate on ordered types and $\mathrm{Contact}_a$ contact predicates. Assume each good type $a=(i,j,k)$ has, near $(p_i,p_j,p_k)$, the supporting inequality $v_i+v_j+v_k\le c$ with equality iff $\mathrm{Contact}_a$, and each bad type has a strict inequality at the centers. Then there are $r,M>0$ such that, with $U_i=B(p_i,r)$ and $u=\sum_i\mathbf{1}_{U_i}v_i$:
--
--   1. $U_i\subseteq V_i$, the $U_i$ are pairwise disjoint, and $u$ is measurable, continuous on $\bigcup U_i$, with $|u|\le M$;
--   2. for $x,y,z\in\bigcup_iU_i$,
--   $$
--   u(x)+u(y)+u(z)\le c(x,y,z),
--   $$
--      with equality iff $(x,y,z)$ is a component contact of a good type.
--
--   Local certificates at good types and strict gaps elsewhere glue into one bounded measurable supporting potential.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/GluedCertificate.lean#L22-L98

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

open OAI OAI.Problem356
universe uIndex
open Set Filter Metric
open scoped ENNReal BigOperators

theorem OAI.Problem356.exists_glued_component_certificate {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (hp : Function.Injective p)
    (V : ι → Set E3) (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (v : ι → E3 → ℝ) (hv : ∀ i, ContinuousOn (v i) (V i))
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop)
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Contact a t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (p i) r
      let u := ComponentPotential.glue U v
      (∀ i, U i ⊆ V i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) ↔
          componentContact U Good Contact (x, (y, z)))) := by sorry
