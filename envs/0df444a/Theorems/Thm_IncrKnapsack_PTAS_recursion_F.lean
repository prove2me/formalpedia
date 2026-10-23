-- Prove2me | Theorems.Thm_IncrKnapsack_PTAS_recursion_F
-- name    : IncrKnapsack.PTAS.recursion_F
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:16.500641+00:00
-- url     : https://prove2.me/theorems/ef52b3d6-1f01-4557-a75b-4743a4c5dcb2
-- title:
--   Recursive equations, §3.4, p. 25 — F(m, ℓ_m, ϕ_m) is the attained minimum of F(m − 1, ℓ_{m−1}, ϕ_{m−1}) + OPT(I_single)
-- statement:
--   Let an incremental knapsack instance satisfy the standing assumptions, let $\epsilon = 1/K$ with $K > 4$ an integer, let $\xi \in \{0,\dots,K-1\}$, and work with the rounded profits of §2.2. For every cluster index $m \ge 1$, class index $\ell_m \ge 0$ and profit $\varphi_m$, the exact value function satisfies the recursion
--
--   $$F(m, \ell_m, \varphi_m) = \min_{\substack{\ell_{m-1} \in \{-1, 0, \dots, \ell_m\}\\ \varphi_{m-1} \in [0, \varphi_m]}} \Big\{ F(m-1, \ell_{m-1}, \varphi_{m-1}) + \mathrm{OPT}\big(\mathcal I^{\phi,\omega}_{\mathrm{single}}[m, \ell_{m-1}+1, \ell_m]\big) \Big\},$$
--
--   where $\phi = \varphi_m - \varphi_{m-1}$ and $\omega = F(m-1, \ell_{m-1}, \varphi_{m-1})$. Precisely:
--
--   1. for every admissible pair $(\ell_{m-1}, \varphi_{m-1})$ the bracket is at least $F(m, \ell_m, \varphi_m)$;
--   2. if $\varphi_m \ge 0$ and $F(m, \ell_m, \varphi_m) < \infty$, some admissible pair attains equality.
--
--   The recursion turns the characterization of optimal uncrossing-stars solutions into a dynamic program over clusters. The approximate program $\tilde F$ of §3.5 mimics it.
--
--   **Formalization Note.** The minimum is stated as a lower bound plus attainment, never as an infimum. The predecessor class index ranges over $\{-1, \dots, \ell_m\}$; page 25 prints $[\ell_m]_0$, but $-1$ is needed, since it is the paper's own convention $\tilde\ell_0 = -1$ and without it cluster 1 could never use $\mathcal P_0$. When $F(m-1,\cdot,\cdot) = \infty$, the real value passed as $\omega$ is immaterial because the bracket is already $\infty$. Clusters and classes are shifted in Lean (`m + 1`, `j + 1`).
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, p. 25, §3.4, equation (6) and 'Recursive equations'

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

namespace IncrKnapsack.PTAS

theorem recursion_F (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (m j : ℕ) (ϕ : ℝ) :
    (∀ j' : ℕ, j' ≤ j + 1 → ∀ ϕ' : ℝ, 0 ≤ ϕ' → ϕ' ≤ ϕ →
        F I K ξ (m + 1) (j + 1) ϕ ≤
          F I K ξ m j' ϕ' +
            OPTsingle I K ξ (m + 1) j' j (ϕ - ϕ') ((F I K ξ m j' ϕ').untopD 0)) ∧
      (0 ≤ ϕ → F I K ξ (m + 1) (j + 1) ϕ < ⊤ →
        ∃ j' : ℕ, j' ≤ j + 1 ∧ ∃ ϕ' : ℝ, 0 ≤ ϕ' ∧ ϕ' ≤ ϕ ∧
          F I K ξ (m + 1) (j + 1) ϕ =
            F I K ξ m j' ϕ' +
              OPTsingle I K ξ (m + 1) j' j (ϕ - ϕ') ((F I K ξ m j' ϕ').untopD 0)) := by sorry
end IncrKnapsack.PTAS
