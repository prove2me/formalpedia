-- Prove2me | Theorems.Thm_LLLFactor_Reduction_gram_lower_bound
-- name    : LLLFactor.Reduction.gram_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:39.274791+00:00
-- url     : https://prove2.me/theorems/70d63b87-df09-4f4e-9ea5-1d8808230ff8
-- title:
--   (1.23), p. 522 — m(L) > 0 is attained and d_i ≥ (3/4)^{i(i−1)/2} m(L)^i for every basis of L
-- statement:
--   Let $n\ge1$, let $L\subset\mathbb R^n$ be a lattice and $c_1,\dots,c_n$ a basis for $L$. Put $m(L)=\min\{|x|^2:x\in L,\ x\ne0\}$. Then $m(L)$ is a positive real number, it is attained by a non-zero vector of $L$, and the Gram determinants $d_i=\det\big((c_j,c_l)\big)_{1\le j,l\le i}$ satisfy
--   $$d_i\ \ge\ \left(\tfrac34\right)^{i(i-1)/2} m(L)^i\qquad(1\le i\le n).$$
--
--   The bound depends only on $L$, not on the basis; since every basis met by the algorithm is a basis for $L$, it gives the positive lower bound for $D$ on which termination rests.
--
--   **Formalization Note.** $m(L)$ is written as the infimum of $\{|x|^2 : x\in L,\ x\ne 0\}$; the statement asserts that this infimum is attained. The exponent $i(i-1)/2$ is a natural number, so it is a natural-number power.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 522, (1.23)

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

namespace LLLFactor.Reduction

theorem gram_lower_bound {n : ℕ} (hn : 0 < n) (c : Fin n → LLLFactor.RedBasis.Vec n)
    (L : Submodule ℤ (LLLFactor.RedBasis.Vec n)) (hc : LLLFactor.RedBasis.IsBasisFor c L) :
    0 < minSqNorm L ∧
    (∃ x ∈ L, x ≠ 0 ∧ ‖x‖ ^ 2 = minSqNorm L) ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ n →
      (3 / 4 : ℝ) ^ (i * (i - 1) / 2) * minSqNorm L ^ i ≤ gram c i := by sorry

end LLLFactor.Reduction
