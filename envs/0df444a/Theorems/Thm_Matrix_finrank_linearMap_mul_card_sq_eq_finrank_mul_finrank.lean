-- Prove2me | Theorems.Thm_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank
-- name    : Matrix.finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/a1c7f9bf-ae1f-5528-8fb4-39e558446c72
-- title:
--   Dimension form of Morita equivalence for Mₙ(k)
-- statement:
--   Let $k$ be a field, let $\iota$ be a finite type with decidable equality, and write $M_\iota(k)$ for the ring `Matrix ι ι k` of $\iota\times\iota$ matrices over $k$. Let $V$ and $W$ be additive commutative groups, each carrying both a $k$-module structure and an $M_\iota(k)$-module structure, the two being compatible in the sense that the $k$-action is obtained from the $M_\iota(k)$-action along the scalar-matrix map (`IsScalarTower k (Matrix ι ι k)` for each of $V$ and $W$), and suppose that $V$ and $W$ are finite-dimensional as $k$-vector spaces. Consider the space $V \to_{M_\iota(k)} W$ of $M_\iota(k)$-linear maps from $V$ to $W$, regarded as a $k$-vector space via the compatible $k$-action. The assertion is the equality of natural numbers
--   $$\dim_k \operatorname{Hom}_{M_\iota(k)}(V,W)\cdot |\iota|^{2} = \dim_k V\cdot \dim_k W,$$
--   where $\dim_k$ denotes `Module.finrank` over $k$ and $|\iota|$ is the cardinality of $\iota$.
--
--   This is the dimension-counting form of the Morita equivalence between $k$ and the matrix algebra $M_\iota(k)$: every such module is a direct sum of copies of the column module, and $\operatorname{Hom}$ over $M_\iota(k)$ has dimension $(\dim_k V/|\iota|)(\dim_k W/|\iota|)$. It is used in the study of maximal orders in quaternion algebras, where for $|\iota| = 2$ and $\dim_k V = \dim_k W = 2$ it forces the space of $M_2(k)$-linear maps to be one-dimensional.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w w'

theorem Matrix.finrank_linearMap_mul_card_sq_eq_finrank_mul_finrank
    (k : Type u) [Field k] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (V : Type w) (W : Type w') [AddCommGroup V] [Module k V] [Module (Matrix ι ι k) V]
    [IsScalarTower k (Matrix ι ι k) V]
    [AddCommGroup W] [Module k W] [Module (Matrix ι ι k) W] [IsScalarTower k (Matrix ι ι k) W]
    [FiniteDimensional k V] [FiniteDimensional k W] :
    Module.finrank k (V →ₗ[Matrix ι ι k] W) * Fintype.card ι ^ 2 =
      Module.finrank k V * Module.finrank k W := by sorry
