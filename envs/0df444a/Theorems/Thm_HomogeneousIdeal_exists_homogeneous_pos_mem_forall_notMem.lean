-- Prove2me | Theorems.Thm_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem
-- name    : HomogeneousIdeal.exists_homogeneous_pos_mem_forall_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/8b79213d-aaa1-5f6a-bc1f-6e5fb136798b
-- title:
--   Graded prime avoidance for homogeneous ideals
-- statement:
--   Let $A$ be a commutative ring carrying an $\mathbb{N}$-grading $\mathcal{A} : \mathbb{N} \to \sigma$ in Mathlib's sense (`GradedRing 𝒜`), where $\sigma$ is any `SetLike` family of additive subgroups of $A$. Let $I$ be a homogeneous ideal of $A$ contained in the irrelevant homogeneous ideal $\mathcal{A}_+ = \bigoplus_{n>0}\mathcal{A}_n$, i.e. every element of $I$ has vanishing degree-$0$ component. Let $t$ be a finite set of homogeneous ideals of $A$ such that, for each $p \in t$, the underlying ideal `p.toIdeal` is prime, and such that $I \not\le p$ for each $p \in t$. Then there are a natural number $n$ and an element $x \in A$ with $n > 0$, $x \in \mathcal{A}_n$, $x \in I$, and $x \notin p$ for every $p \in t$. Thus $I$ contains a homogeneous element of strictly positive degree avoiding all the given homogeneous primes. Note that $t$ is a finite set of homogeneous ideals, so homogeneity of the avoided primes is built into the indexing type rather than being a separate hypothesis.
--
--   This is graded (homogeneous) prime avoidance, the graded counterpart of the usual statement that an ideal not contained in any of finitely many primes contains an element outside their union. It is used in the construction of affine opens of $\operatorname{Proj}\mathcal{A}$ containing a prescribed finite set of relevant homogeneous primes, and is cited by [`AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj`](thm.html#AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj), [`AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isImmersion_proj`](thm.html#AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isImmersion_proj) and [`AlgebraicGeometry.exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj`](thm.html#AlgebraicGeometry.exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HomogeneousIdeal.exists_homogeneous_pos_mem_forall_notMem
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (I : HomogeneousIdeal 𝒜) (hirr : I ≤ HomogeneousIdeal.irrelevant 𝒜)
    (t : Finset (HomogeneousIdeal 𝒜)) (hprime : ∀ p ∈ t, p.toIdeal.IsPrime) (havoid : ∀ p ∈ t, ¬ I ≤ p) :
    ∃ (n : ℕ) (x : A), 0 < n ∧ x ∈ 𝒜 n ∧ x ∈ I ∧ ∀ p ∈ t, x ∉ p := by sorry
