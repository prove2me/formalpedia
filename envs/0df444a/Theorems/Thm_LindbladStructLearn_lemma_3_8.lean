-- Prove2me | Theorems.Thm_LindbladStructLearn_lemma_3_8
-- name    : LindbladStructLearn.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:00:18.932381+00:00
-- url     : https://prove2.me/theorems/a9b947f5-ae14-4217-98f2-8289a0260701
-- title:
--   Lemma 3.8 — $\|A_k\|_{B_1\to B_1} \le 4^k$ and $\|A_k^{-1}\|_{B_1\to B_1} \le 4^k$
-- statement:
--   Let $A = A_k$ for $0 \le k \le n$. Then for every vector $x$ on the $k$-local pairs,
--
--   $$\|Ax\|_\infty \le \|Ax\|_{B_1} \le 4^k\|x\|_{B_1}, \qquad \|A^{-1}x\|_\infty \le \|A^{-1}x\|_{B_1} \le 4^k\|x\|_{B_1},$$
--
--   i.e. $\|A\|_{B_1\to\infty} \le \|A\|_{B_1\to B_1} \le 4^k$ and $\|A^{-1}\|_{B_1\to\infty} \le \|A^{-1}\|_{B_1\to B_1} \le 4^k$.
--
--   The bounds keep the update $x \leftarrow x - A^{-1}\widehat{\mathcal F}(x)$ stable in the local one-norm.
--
--   Differences from the source:
--   - encoding: operator norms ‖A‖_{B1→∞} ≤ ‖A‖_{B1→B1} ≤ 4^k (and for A⁻¹) → for every x: ‖Ax‖_∞ ≤ ‖Ax‖_B1 ≤ 4^k‖x‖_B1 (and for A⁻¹); reason: ‖A‖_{a→b} ≤ c is equivalent to the vector inequalities; the vector form of the first inequality implies the norm form
--   - encoding: A⁻¹ → Mathlib's matrix inverse of A_k; reason: A_k is invertible (Corollary 3.7)
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Lemma 3.8, Eqs. (3.38)–(3.39), p.22

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_Amat
import Definitions.Def_LindbladStructLearn_ext
import Definitions.Def_LindbladStructLearn_b1Norm

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Lemma 3.8 (`A_k` is well-behaved; Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eqs. (3.38)–(3.39), p.22): for `A = A_k`,
`0 ≤ k ≤ n`, `‖A‖_(B1→∞) ≤ ‖A‖_(B1→B1) ≤ 4^k` and `‖A⁻¹‖_(B1→∞) ≤ ‖A⁻¹‖_(B1→B1) ≤ 4^k`.

**Formalization Note** The operator norms are stated vector by vector: for every `x`,
`‖Ax‖_∞ ≤ ‖Ax‖_B1 ≤ 4^k‖x‖_B1`, and the same for `A⁻¹` (Mathlib's matrix inverse). This gives both
printed chains (the first inequality of each chain from `‖y‖_∞ ≤ ‖y‖_B1` for every `y`). `‖·‖_∞` is
the sup norm of `ℂ^m`; `‖·‖_B1` is applied to the zero extension. -/
theorem lemma_3_8 (n k : ℕ) (hkn : k ≤ n) (x : Idx n k → ℂ) :
    (‖Matrix.mulVec (Amat n k) x‖ ≤ b1Norm (ext (Matrix.mulVec (Amat n k) x)) ∧
      b1Norm (ext (Matrix.mulVec (Amat n k) x)) ≤ 4 ^ k * b1Norm (ext x)) ∧
    (‖Matrix.mulVec (Amat n k)⁻¹ x‖ ≤ b1Norm (ext (Matrix.mulVec (Amat n k)⁻¹ x)) ∧
      b1Norm (ext (Matrix.mulVec (Amat n k)⁻¹ x)) ≤ 4 ^ k * b1Norm (ext x)) := by sorry

end LindbladStructLearn
