-- Prove2me | Theorems.Thm_IncrKnapsack_PTAS_claim_2
-- name    : IncrKnapsack.PTAS.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:33.020983+00:00
-- url     : https://prove2.me/theorems/de1077f2-06d5-4008-9c95-87633b2de2de
-- title:
--   Claim 2, p. 28 (proof A.4) — the glued solution earns Ψ(S̄) ≥ (1 − 2ε)·ϕ̃_M − Mδ
-- statement:
--   Let an incremental knapsack instance satisfy the standing assumptions, let $\epsilon = 1/K$ with $K > 4$ an integer, let $\xi \in \{0,\dots,K-1\}$, and work with the rounded profits of §2.2. Let $\Phi$ be a profit grid, let $\mathcal A$ be a single-cluster subroutine with the guarantee of Theorem 3, and let $\bar{\mathcal S}$ be the solution glued along any traceback of $\tilde F$ from $(M, L, \tilde\varphi_M)$. Here $\tilde\varphi_M$ is the largest grid value with $\tilde F(M, L, \tilde\varphi_M) < \infty$. Then, with $\delta = (\epsilon/M)\lambda_T p_{\max}$,
--
--   $$\Psi(\bar{\mathcal S}) \ge (1-2\epsilon)\cdot\tilde\varphi_M - M\delta.$$
--
--   This converts the profit parameter reached by the approximate program into a guaranteed profit of the constructed solution. With Claim 3 and Corollary 1 it gives Lemma 11.
--
--   **Formalization Note.** Only the nonnegativity of grid values is used from the grid hypothesis. $M$ is the number of clusters for the shift $\xi$; when $M = 0$ the right-hand side is $0$.
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, p. 28, Claim 2; proof in Appendix A.4, pp. 34–35

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

namespace IncrKnapsack.PTAS

theorem claim_2 (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Φ : Finset ℝ) (A : Subroutine I) (jt : ℕ → ℕ) (ϕt : ℕ → ℝ)
    (hΦ : IsProfitGrid I K ξ Φ) (hA : IsSubroutine I K ξ A) (htr : IsTraceback I K ξ Φ A jt ϕt) :
    (1 - 2 * eps K) * ϕt (Mcl I K ξ) - (Mcl I K ξ : ℝ) * delta I K ξ ≤
      Psi I (pr I K) (algOut I K ξ Φ A jt ϕt) := by sorry
end IncrKnapsack.PTAS
