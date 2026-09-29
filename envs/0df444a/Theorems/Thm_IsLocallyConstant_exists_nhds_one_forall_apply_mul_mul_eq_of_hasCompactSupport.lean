-- Prove2me | Theorems.Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
-- name    : IsLocallyConstant.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/0539b98f-7e8a-5562-a5e5-0d1171d7060a
-- title:
--   Uniform two-sided invariance of compactly supported locally constant functions
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group (so multiplication and inversion are continuous), let $Y$ be a type equipped with a distinguished element $0$, and let $f : G \to Y$ be a function which is locally constant, i.e. every fibre $f^{-1}(y)$ is open, and which has compact support, i.e. the closure of $\{g : f(g) \neq 0\}$ is compact. The conclusion is that there exists a set $V$ belonging to the neighbourhood filter of the identity $1 \in G$ such that for all $u \in V$, all $u' \in V$ and all $g \in G$ one has $f(u g u') = f(g)$. Thus the local constancy of $f$ is uniform over all of $G$ and two-sided: a single neighbourhood of $1$ works simultaneously for every argument $g$, and perturbing $g$ by elements of $V$ on both the left and the right does not change the value of $f$. Note that $V$ is only asserted to be a neighbourhood of $1$; no subgroup, no openness of $V$, and no local compactness or total disconnectedness of $G$ is claimed or assumed.
--
--   This is the basic smoothness statement underlying the Hecke algebra of a locally profinite group: a locally constant compactly supported test function is bi-invariant under small perturbations of its argument, and on a group with a basis of compact open subgroups at the identity this yields bi-invariance under such a subgroup. It is used in the automorphic part of the argument, for instance in the treatment of orbital integrals and of right convolution on spaces of cusp forms, where one needs a single neighbourhood of the identity controlling a test function uniformly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport.lean

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.LocallyConstant.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsLocallyConstant.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) :
    ∃ V ∈ nhds (1 : G), ∀ u ∈ V, ∀ u' ∈ V, ∀ g : G, f (u * g * u') = f g := by sorry
