-- Prove2me | Theorems.Thm_LiqPremiaEq_lemma_7_4
-- name    : LiqPremiaEq.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:01.400979+00:00
-- url     : https://prove2.me/theorems/62027aff-61a1-4b71-b298-9aaa1609b169
-- title:
--   Lemma 7.4 — $A\otimes B$ is positive semidefinite if $A,B$ are and $B$ is symmetric
-- statement:
--   Let $A$ and $B$ be square real matrices that are positive semidefinite in the sense $b^\top Ab\ge0$ for all $b$ (no symmetry), and suppose $B$ is symmetric. Then the Kronecker product $A\otimes B$ is positive semidefinite:
--
--   $$x^\top(A\otimes B)x\ge0\qquad\text{for all } x.$$
--
--   The matrix $A$ need not be symmetric. The lemma is applied with $A=\Gamma$ and $B=\sigma_H\sigma_H^\top$ in the proof of Corollary 7.7.
--
--   Differences from the source:
--   - reading: positive (semi)definite → IsPSDQuad A: bᵀAb ≥ 0 for all b (IsPDQuad: bᵀAb > 0 for b ≠ 0), no symmetry required; reason: footnotes 10 (p.8) and 19 (p.14): the matrices are not symmetric and the notions are meant without symmetry
--   - encoding: matrices A, B of arbitrary size → A : Matrix ι ι ℝ, B : Matrix κ κ ℝ over arbitrary finite index types, A ⊗ B = kroneckerMap (· * ·) A B; reason: the same statement for every size
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Lemma 7.4, p.17

import Mathlib
import Definitions.Def_LiqPremiaEq_IsPSDQuad

open Matrix
open scoped Kronecker

namespace LiqPremiaEq

/-- **Lemma 7.4.** If the square matrices `A` and `B` are positive semidefinite (`bᵀAb ≥ 0`,
without symmetry) and `B` is symmetric, then the Kronecker product `A ⊗ B` is positive
semidefinite.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Lemma 7.4, p.17.

**Formalization Note** `A` need not be symmetric. Index types are arbitrary finite types;
`A ⊗ B` is Mathlib's `kroneckerMap (· * ·) A B`. -/
theorem lemma_7_4 {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : IsPSDQuad A) (hB : IsPSDQuad B) (hBsymm : Bᵀ = B) :
    IsPSDQuad (A ⊗ₖ B) := by sorry

end LiqPremiaEq
