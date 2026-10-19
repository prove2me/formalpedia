-- Prove2me | Theorems.Thm_OAI_Problem356_finite_component_certificate
-- name    : OAI.Problem356.finite_component_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:03:16.145043+00:00
-- url     : https://prove2.me/theorems/f30b5026-0e01-4867-86e9-5988762a689a
-- title:
--   From local and center certificates to a certificate on component balls
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. A three-coupling of $\mu$ is a probability measure on triples with all three marginals $\mu$, and the Kantorovich value is the infimum of $\int c\,d\pi$ over three-couplings. Let $(p_i)_{i\in\iota}$ be finitely many centers with potentials $v_i$ continuous at $p_i$, a predicate $\mathrm{Good}$ on ordered types and contact predicates $\mathrm{Contact}_a$. Assume:
--
--   1. for good types $a=(i,j,k)$, near $(p_i,p_j,p_k)$ the potential sum is $\le c$, with equality iff $\mathrm{Contact}_a$;
--   2. for every other type the inequality is strict at the centers.
--
--   Then there is $r>0$ such that for every type $a$ and all $x\in B(p_i,r)$, $y\in B(p_j,r)$, $z\in B(p_k,r)$,
--   $$
--   v_i(x)+v_j(y)+v_k(z)\le c(x,y,z),
--   $$
--   with equality iff $a$ is good and $\mathrm{Contact}_a(x,y,z)$.
--
--   This is the local-to-global step: supporting inequalities are only needed near good types, and strict gaps handle all others.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/ComponentCertificate.lean#L68-L105

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

open OAI OAI.Problem356
universe uIndex
open Set Filter Metric
open scoped ENNReal BigOperators

theorem OAI.Problem356.finite_component_certificate {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (v : ι → E3 → ℝ)
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop)
    (hv : ∀ i, ContinuousAt (v i) (p i))
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Contact a t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r : ℝ, 0 < r ∧ ∀ a, ∀ x y z : E3,
      x ∈ ball (p a.1) r → y ∈ ball (p a.2.1) r → z ∈ ball (p a.2.2) r →
      ENNReal.ofReal (v a.1 x + v a.2.1 y + v a.2.2 z) ≤ coulombCost (x, (y, z)) ∧
      (ENNReal.ofReal (v a.1 x + v a.2.1 y + v a.2.2 z) = coulombCost (x, (y, z)) ↔
        Good a ∧ Contact a (x, (y, z))) := by sorry
