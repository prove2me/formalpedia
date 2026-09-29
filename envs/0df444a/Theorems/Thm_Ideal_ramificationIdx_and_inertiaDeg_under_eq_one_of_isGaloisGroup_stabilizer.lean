-- Prove2me | Theorems.Thm_Ideal_ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
-- name    : Ideal.ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/0bd41aa1-0c60-573d-a8a8-6dd1cf6e5f14
-- title:
--   Decomposition subring: e(P∩ C∣𝔭)=f=1
-- statement:
--   Let $A$, $B$, $C$ be commutative rings that are Dedekind domains, equipped with algebra structures $A\to B$, $A\to C$, $C\to B$ forming a scalar tower $A\to C\to B$, and assume $B$ is finite and torsion-free as a module over $A$ and also over $C$. Let $G$ be a finite group acting on $B$ by ring automorphisms (a `MulSemiringAction`) such that `IsGaloisGroup G A B` holds, i.e. $G$ realises $B$ as a Galois extension of $A$ in Mathlib's sense. Let $\mathfrak p$ be a maximal ideal of $A$ with $\mathfrak p\neq\bot$, and let $\mathfrak P$ be a maximal ideal of $B$ lying over $\mathfrak p$, with the residue field extension $(A/\mathfrak p)\to(B/\mathfrak P)$ separable. Assume finally that the stabiliser $\operatorname{Stab}_G(\mathfrak P)$, acting on $B$ by restriction of the $G$-action, satisfies `IsGaloisGroup (MulAction.stabilizer G P) C B`. Then the ideal $\mathfrak P\cap C$ (the contraction `P.under C` of $\mathfrak P$ along $C\to B$) has ramification index and residue degree one over $\mathfrak p$: $e'(\mathfrak p,\mathfrak P\cap C)=1$ and $f'(\mathfrak p,\mathfrak P\cap C)=1$, in the primed (`ramificationIdx'`, `inertiaDeg'`) normalisations.
--
--   This is the classical statement of Hilbert's ramification theory that the decomposition field of $\mathfrak P$ is unramified over $\mathfrak p$ with residue degree one, here in the form: if $C$ is the invariant subring of the decomposition group $\operatorname{Stab}_G(\mathfrak P)$, then $\mathfrak P\cap C$ has $e=f=1$ over $\mathfrak p$. It is used in the project's local computations, for instance in the comparison of Swan conductors under restriction to a normal subgroup and in a statement about irreducibility of images of integers in valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise

theorem Ideal.ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [Module.Finite A B] [Module.IsTorsionFree A B] [Module.Finite C B] [Module.IsTorsionFree C B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (p : Ideal A) (hp : p ≠ ⊥) [p.IsMaximal] (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [IsGaloisGroup (MulAction.stabilizer G P) C B] :
    p.ramificationIdx' (P.under C) = 1 ∧ p.inertiaDeg' (P.under C) = 1 := by sorry
