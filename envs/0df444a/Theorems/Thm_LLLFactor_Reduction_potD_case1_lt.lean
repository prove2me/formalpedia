-- Prove2me | Theorems.Thm_LLLFactor_Reduction_potD_case1_lt
-- name    : LLLFactor.Reduction.potD_case1_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:26.254243+00:00
-- url     : https://prove2.me/theorems/ba0c246a-c24f-4308-9072-596855a1a6b4
-- title:
--   (1.23), p. 521 — in case 1, d_{k−1} drops by a factor < ¾ and the other d_i are unchanged, so D drops by a factor < ¾; case 2 changes no d_i
-- statement:
--   Let $b_1,\dots,b_n\in\mathbb R^n$ be linearly independent, let $d_i$ be the Gram determinants (1.24) and $D=\prod_{i=1}^{n-1}d_i$.
--
--   1. If a step of case 1 of the algorithm (1.15) leads from $(b,k)$ to $(b',k-1)$, then
--   $$d_{k-1}(b')<\tfrac34\,d_{k-1}(b),\qquad d_i(b')=d_i(b)\ \ (0\le i\le n,\ i\ne k-1),\qquad D(b')<\tfrac34\,D(b).$$
--   2. If a step of case 2 leads from $(b,k)$ to $(b',k+1)$, then $d_i(b')=d_i(b)$ for $0\le i\le n$.
--
--   This is the potential argument of (1.23): "the number $D$ only changes if some $b_i^*$ is changed, which only occurs in case 1. In case 1, the number $d_{k-1}$ is reduced by a factor $<\tfrac34$ … whereas the other $d_i$ are unchanged … hence $D$ is reduced by a factor $<\tfrac34$."
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 521, (1.23)

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

namespace LLLFactor.Reduction

theorem potD_case1_lt {n : ℕ} (b b' : Fin n → LLLFactor.RedBasis.Vec n) (k k' : ℕ)
    (hb : LinearIndependent ℝ b) :
    (Case1 (b, k) (b', k') →
      gram b' (k - 1) < (3 / 4 : ℝ) * gram b (k - 1) ∧
      (∀ i : ℕ, i ≤ n → i ≠ k - 1 → gram b' i = gram b i) ∧
      potD b' < (3 / 4 : ℝ) * potD b) ∧
    (Case2 (b, k) (b', k') → ∀ i : ℕ, i ≤ n → gram b' i = gram b i) := by sorry

end LLLFactor.Reduction
