-- Prove2me | Theorems.Thm_IsReduced_of_finrank_le_natCard_algHom
-- name    : IsReduced.of_finrank_le_natCard_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/4195ccee-2164-52f3-86c5-3485fe119a6f
-- title:
--   Finite algebras with dim_K B points to K are reduced
-- statement:
--   Let $K$ be a field and $B$ a commutative ring equipped with a $K$-algebra structure such that $B$ is a finite $K$-module (i.e. finitely generated, hence finite-dimensional over the field $K$). Assume that the $K$-dimension of $B$ is at most the cardinality, in the sense of `Nat.card` applied to the type $B \to_{\text{alg}[K]} K$ of $K$-algebra homomorphisms $B \to K$, of the set of such homomorphisms; note that `Nat.card` returns $0$ for an infinite type, so the hypothesis then forces $\dim_K B = 0$. The conclusion is that $B$ is reduced, that is, every nilpotent element of $B$ is zero. No assumption is made on the characteristic of $K$ or on $K$ being separably or algebraically closed, and $B$ is not assumed to be a product of fields or even nonzero.
--
--   This is the converse direction of Dedekind's bound on the number of characters of a finite-dimensional algebra: linear independence of distinct algebra homomorphisms gives $\#\operatorname{Hom}_{K\text{-alg}}(B,K) \le \dim_K B$, and equality (here, the reverse inequality) forces $B$ to be reduced. It is used to deduce reducedness, and thence étaleness, of fibres of coarse moduli models from point counts, and also in the Hopf-algebra bookkeeping of [`HopfAlgebra.map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq`](thm.html#HopfAlgebra.map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsReduced_of_finrank_le_natCard_algHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsReduced.of_finrank_le_natCard_algHom (K B : Type*) [Field K] [CommRing B] [Algebra K B] [Module.Finite K B] (h : Module.finrank K B ≤ Nat.card (B →ₐ[K] K)) : IsReduced B := by sorry
