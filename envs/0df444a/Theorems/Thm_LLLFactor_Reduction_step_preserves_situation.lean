-- Prove2me | Theorems.Thm_LLLFactor_Reduction_step_preserves_situation
-- name    : LLLFactor.Reduction.step_preserves_situation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:27.6531+00:00
-- url     : https://prove2.me/theorems/8607e740-d9ec-4ed4-92f5-de170d35a37b
-- title:
--   (1.15), pp. 519–520 — after each step we are again in the situation (1.16)–(1.17), with 1 ≤ k ≤ n + 1
-- statement:
--   Let $b_1,\dots,b_n\in\mathbb R^n$ be linearly independent and suppose that at subscript $k$ the conditions (1.16) and (1.17) hold:
--   $$|\mu_{ij}|\le\tfrac12\ \ (1\le j<i<k),\qquad |b_i^*+\mu_{i,i-1}b_{i-1}^*|^2\ge\tfrac34|b_{i-1}^*|^2\ \ (1<i<k).$$
--   If one step of the algorithm (1.15) leads from $(b,k)$ to $(b',k')$, then (1.16) and (1.17) hold for $b'$ at subscript $k'$, and $1\le k'\le n+1$.
--
--   This is the sentence ending both cases of (1.15): "Then we are in the situation described by (1.16) and (1.17), and we proceed with the algorithm from there." It is the loop invariant of the algorithm.
--
--   **Formalization Note.** The bound $1\le k'\le n+1$ is the paper's "at each step of the algorithm we shall have a current subscript $k\in\{1,2,\dots,n+1\}$".
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), pp. 519–520, (1.15)–(1.17)

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

namespace LLLFactor.Reduction

theorem step_preserves_situation {n : ℕ} (b b' : Fin n → LLLFactor.RedBasis.Vec n) (k k' : ℕ)
    (hb : LinearIndependent ℝ b) (hsit : Situation b k)
    (hstep : Step (b, k) (b', k')) :
    Situation b' k' ∧ 1 ≤ k' ∧ k' ≤ n + 1 := by sorry

end LLLFactor.Reduction
