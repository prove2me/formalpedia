-- Prove2me | Theorems.Thm_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul
-- name    : Module.free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/1177cb4a-c42f-5995-a8a3-f5eed7dc77a9
-- title:
--   Degree of a power of a finite map: rank nm
-- statement:
--   Let $R$ be a commutative ring and $A$ a commutative $R$-algebra, let $a \in A$, and let $m, n$ be natural numbers with $1 \le n$. Assume that the ring homomorphism underlying the $R$-algebra map $\mathrm{aeval}\,a : R[X] \to A$ sending $X$ to $a$ is finite, i.e. $A$ is module-finite over $R[X]$ through $X \mapsto a$. Assume further the hypothesis $h$: for every commutative local $R$-algebra $S$ (in the same universe) and every $s \in S$, the quotient ring $(S \otimes_R A)/(1 \otimes a - s \otimes 1)$ is a finite, free $S$-module whose rank (`Module.finrank`) equals $m$. Then for every commutative local $R$-algebra $S$ and every $s \in S$, the quotient ring $(S \otimes_R A)/(1 \otimes a^n - s \otimes 1)$ is likewise a finite and free $S$-module, of rank $n \cdot m$. The hypothesis $h$ is quantified over all local $R$-algebras and all elements $s$, and the conclusion is asserted for the one pair $(S, s)$ appearing as the final arguments.
--
--   In geometric terms: if $a \colon \operatorname{Spec} A \to \mathbb{A}^1_R$ is finite locally free of degree $m$, then its composite with $t \mapsto t^n$, namely $a^n$, is finite locally free of degree $nm$, stated here fibrewise over local base algebras in terms of freeness and rank of the level-set rings. It serves the study of finite maps from smooth proper curves, being used in [`AlgebraicGeometry.SmoothProperCurve.FiniteMapData.forall_exists_le_m_of_one_le`](thm.html#AlgebraicGeometry.SmoothProperCurve.FiniteMapData.forall_exists_le_m_of_one_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped TensorProduct Polynomial

theorem Module.free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (a : A) (m n : ℕ) (hn : 1 ≤ n)
    (hfin : (Polynomial.aeval a : R[X] →ₐ[R] A).toRingHom.Finite)
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) = m)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) = n * m := by sorry
