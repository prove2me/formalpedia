-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_theorem_10
-- name    : HetExponomial.ChoiceProb.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:41:46.372179+00:00
-- url     : https://prove2.me/theorems/0a88d800-1c5f-4c3a-8093-6424e0e1c0ed
-- title:
--   Theorem 10, p. 30 — the sequential FOC algorithm (Steps 1–4, any argmin) is well defined and outputs the unique Nash equilibrium
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. In the pricing model, product $i$ has ideal utility $u_i=\alpha_i-\beta p_i$ at price $p_i$, with intrinsic desirability $\alpha_i\in\mathbb R$ and price sensitivity $\beta>0$; market size is $1$ and marginal costs are $0$. In the $n$-firm oligopoly, firm $i$ sells product $i$, chooses a price $p_i\ge 0$ (equivalently $u_i\le\alpha_i$) and earns $R_i=p_i\,Q_i$. A **Nash equilibrium in prices** is a price vector $p^*\ge 0$ from which no firm can raise its revenue by changing its own price to any other nonnegative price; $u^*_i=\alpha_i-\beta p^*_i$, $Q^*_i$ and $R^*_i$ are the equilibrium ideal utilities, market shares and revenues. The ratio $\tau_i(\mathbf u)=Q_i(\mathbf u)/(\partial Q_i(\mathbf u)/\partial u_i)$ is (12), $L=\sum_{k\in N}\lambda_k$, $M=\max_{j}\alpha_j$, and for a set $S$ of solved products with values $u^*_k$, $\tau_i(u_i\mid u(S))$ is $\tau_i$ evaluated with coordinate $i$ equal to $u_i$, coordinate $k\in S$ equal to $u^*_k$, and every other coordinate equal to $M$ (13). Consider the algorithm:
--
--   1. Step 1: $S=\emptyset$, $M=\max_j\alpha_j$, $\mathbf u^*=(M,\dots,M)$, $t=1$.
--   2. Step 2: compute $u^1_i=\alpha_i-1/(L-\lambda_i)$ for all $i$, pick $k\in\arg\min_i u^1_i$, set $u^*_k=u^1_k$ and $S\leftarrow S\cup\{k\}$.
--   3. Step 3: while $t\le n$ after incrementing $t$, for every unsolved $i\notin S$ solve for the unique $u^t_i$ with $\alpha_i-u^t_i=\tau_i(u^t_i\mid u(S))$, pick $k\in\arg\min_{i\notin S}u^t_i$, set $u^*_k=u^t_k$, $S\leftarrow S\cup\{k\}$.
--   4. Step 4: $p^*_i=(\alpha_i-u^*_i)/\beta$.
--
--   **Theorem 10**: the algorithm can be run, with argmin ties broken arbitrarily; in every run each equation of Step 3 has exactly one solution; and the output $\mathbf p^*$ is a Nash equilibrium in prices and the only one:
--   $$
--   \mathbf p^*\ \text{is the unique Nash equilibrium in prices}.
--   $$
--
--   This is a general method that computes the equilibrium of Theorem 9 by solving $n(n-1)/2$ one-dimensional equations.
--
--   **Formalization Note** A run is an order `σ : Fin n ≃ Fin n` (`σ s` is the product fixed at step $s+1$) together with the final values $u^*$. In Step 3 the vector $(u^*_1,\dots,u^t_i,\dots,u^*_n)$ has $M$ at unsolved coordinates other than $i$, which is `condVec`. The candidates of a step are required to solve their equations for every unsolved product; the conclusion asserts the uniqueness of those solutions.
--
--   Differences from the source:
--   - encoding: the algorithm with "find k := argmin" (ties arbitrary) → every σ : Fin n ≃ Fin n and u* satisfying IsGeneralRun, plus existence of one; reason: quantifying over every run is the paper's arbitrary tie-breaking
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 30, Theorem 10; §6.2, pp. 28–30; (13), p. 29

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem theorem_10 {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) :
    (∃ (σ : Fin n ≃ Fin n) (ustar : Fin n → ℝ), IsGeneralRun α lam σ ustar) ∧
      ∀ (σ : Fin n ≃ Fin n) (ustar : Fin n → ℝ), IsGeneralRun α lam σ ustar →
        (∀ s : Fin n, 0 < s.val → ∀ i, i ∉ solvedBefore σ s.val →
            ∃! x : ℝ, α i - x = tauCond α lam (solvedBefore σ s.val) ustar i x) ∧
          IsPriceNE α β lam (eqPrices α β ustar) ∧
          ∀ p, IsPriceNE α β lam p → p = eqPrices α β ustar := by sorry

end HetExponomial.ChoiceProb.Supplement
