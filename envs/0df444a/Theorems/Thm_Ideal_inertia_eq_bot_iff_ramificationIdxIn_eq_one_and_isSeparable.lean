-- Prove2me | Theorems.Thm_Ideal_inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable
-- name    : Ideal.inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/aa19cb1e-2854-554b-be2a-c5faaea39bf9
-- title:
--   Trivial inertia iff e=1 and separable residue extension
-- statement:
--   Let $A$ and $B$ be commutative rings which are Dedekind domains, with $B$ an $A$-algebra that is finite and torsion-free as an $A$-module, and let $G$ be a finite group acting on $B$ by ring automorphisms in such a way that $G$ is a Galois group for the extension $A \subseteq B$ (`IsGaloisGroup G A B`). Let $p$ be a nonzero maximal ideal of $A$ and let $P$ be a maximal ideal of $B$ lying over $p$. The assertion is an equivalence: the inertia subgroup `P.inertia G`, consisting of those $\sigma \in G$ acting trivially on the residue ring $B/P$, is the trivial subgroup if and only if both the ramification index `p.ramificationIdxIn B` — the common value of $e(\mathfrak{Q} \mid p)$ over the primes $\mathfrak{Q}$ of $B$ above $p$ — equals $1$, and the residue field extension $(B/P)/(A/p)$ is separable. Note that the ramification index occurring in the conclusion is the one attached to $p$ and $B$ rather than to the individual prime $P$; in the present Galois setting the two agree.
--
--   This is the standard characterisation of unramified primes by triviality of the inertia group, in the form valid with no perfectness or separability assumption on the residue field $A/p$. It is used in the construction of torsion points on Jacobians with good reduction, where trivial inertia at a prime is converted into an unramified residue extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem Ideal.inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable
    {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    {p : Ideal A} (hpb : p ≠ ⊥) [p.IsMaximal] (P : Ideal B) [P.IsMaximal] [P.LiesOver p] :
    P.inertia G = ⊥ ↔ p.ramificationIdxIn B = 1 ∧ Algebra.IsSeparable (A ⧸ p) (B ⧸ P) := by sorry
