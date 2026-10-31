-- Prove2me | Theorems.Thm_IncrKnapsack_PTAS_claim_3
-- name    : IncrKnapsack.PTAS.claim_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:13.874884+00:00
-- url     : https://prove2.me/theorems/70baa0f8-4d97-454c-b197-ffea58b40f4b
-- title:
--   Claim 3, p. 28 (proof A.5) — the approximate program lower-bounds the exact one: F̃(m, ℓ_m, ϕ_m) ≤ F(m, ℓ_m, ϕ_m) on the discretized states
-- statement:
--   Let an incremental knapsack instance satisfy the standing assumptions, let $\epsilon = 1/K$ with $K > 4$ an integer, let $\xi \in \{0,\dots,K-1\}$, and work with the rounded profits of §2.2. Let $\Phi$ be a profit grid (see the definitions file), and let $\mathcal A$ be a single-cluster subroutine with the guarantee of Theorem 3: super-optimal weight, (8), and profit at least $(1-\epsilon)\phi$. Then for every state $(m, \ell_m, \varphi_m)$ of the discretized state space $\mathcal D$, i.e. $m \in \{0,\dots,M\}$, $\ell_m \in \{-1,\dots,L\}$ and $\varphi_m \in \Phi$,
--
--   $$\tilde F(m, \ell_m, \varphi_m) \le F(m, \ell_m, \varphi_m).$$
--
--   Discretizing the profit parameter and replacing exact single-cluster optima by the subroutine's super-optimal answers thus never increases the computed weight. Combined with Corollary 1, $\tilde F$ is finite at every grid point up to $(1-2\epsilon)\Psi(\mathcal S^*)$.
--
--   **Formalization Note.** The grid is the hypothesis `IsProfitGrid`. It asks for property (15) of p. 35 on the range $[0, \lambda^{1+}\sum_i p_i]$ that page 22 gives $\varphi_m$, guarded by $M > 0$. It replaces the printed grid (7), whose largest element is about $\lambda^{1+}p_{\max}$ and does not cover that range.
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, p. 28, Claim 3; proof in Appendix A.5, pp. 35–36

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

namespace IncrKnapsack.PTAS

theorem claim_3 (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Φ : Finset ℝ) (A : Subroutine I)
    (hΦ : IsProfitGrid I K ξ Φ) (hA : IsSubroutine I K ξ A) :
    ∀ m : ℕ, m ≤ Mcl I K ξ → ∀ j : ℕ, j ≤ Lmax I K + 1 → ∀ ϕ ∈ Φ,
      Ftil I K ξ Φ A m j ϕ ≤ F I K ξ m j ϕ := by sorry
end IncrKnapsack.PTAS
