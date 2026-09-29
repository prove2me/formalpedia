-- Prove2me | Theorems.Thm_Module_exists_ideal_forall_projective_and_rankAtStalk_eq_iff
-- name    : Module.exists_ideal_forall_projective_and_rankAtStalk_eq_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/f177054b-09b5-551a-a938-94d025607fc8
-- title:
--   Universal ideal for rank-r local freeness after base change
-- statement:
--   Let $A$ be a commutative ring and $M$ a finitely generated $A$-module, and let $r$ be a natural number such that for every prime $\mathfrak p$ of $A$ the fibre $\kappa(\mathfrak p)\otimes_A M$ has dimension at most $r$ over the residue field $\kappa(\mathfrak p)$ of $\mathfrak p$. Then there exists an ideal $\mathfrak a\subseteq A$ with the following universal property: for every commutative ring $B$ equipped with an $A$-algebra structure, the base change $B\otimes_A M$ is a projective $B$-module whose rank at every stalk (i.e. `Module.rankAtStalk` at each prime $\mathfrak q$ of $B$) equals $r$ if and only if $\mathfrak a$ is killed by the structure map, that is, $a \mapsto 0$ in $B$ for every $a\in\mathfrak a$. The ideal $\mathfrak a$ is produced once and for all from $A$, $M$ and $r$, independently of $B$; the statement asserts its existence, not a formula for it.
--
--   This is the Fitting-ideal description of the locus over which a finite module becomes locally free of constant rank $r$: the condition on an $A$-algebra $B$ that $B\otimes_A M$ be projective of rank $r$ everywhere is cut out by a single ideal of $A$, so it is a closed condition representable by $\operatorname{Spec}(A/\mathfrak a)$. It is used in the construction of Hilbert functors, via [`AlgebraicGeometry.HilbertFunctor.exists_ideal_forall_projective_piece_succ_iff`](thm.html#AlgebraicGeometry.HilbertFunctor.exists_ideal_forall_projective_piece_succ_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_ideal_forall_projective_and_rankAtStalk_eq_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Module.exists_ideal_forall_projective_and_rankAtStalk_eq_iff
    (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] (r : ℕ)
    (hr : ∀ p : PrimeSpectrum A,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] M) ≤ r) :
    ∃ 𝔞 : Ideal A, ∀ (B : Type) [CommRing B] [Algebra A B],
      (Module.Projective B (B ⊗[A] M) ∧ ∀ q : PrimeSpectrum B, Module.rankAtStalk (B ⊗[A] M) q = r) ↔
        ∀ a ∈ 𝔞, algebraMap A B a = 0 := by sorry
