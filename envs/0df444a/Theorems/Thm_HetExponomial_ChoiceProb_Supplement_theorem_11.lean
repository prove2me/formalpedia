-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_theorem_11
-- name    : HetExponomial.ChoiceProb.Supplement.theorem_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:42:34.307869+00:00
-- url     : https://prove2.me/theorems/6c75b16c-7367-4e1d-986b-ef21a9637614
-- title:
--   Theorem 11, pp. 31–32 — under α_i + 1/λ_i ≤ α_j + 1/λ_j ⇒ α_i ≤ α_j, the one-pass procedure yields the unique Nash equilibrium, u*_i ≥ u*_{i−1}
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. In the pricing model, product $i$ has ideal utility $u_i=\alpha_i-\beta p_i$ at price $p_i$, with intrinsic desirability $\alpha_i\in\mathbb R$ and price sensitivity $\beta>0$; market size is $1$ and marginal costs are $0$. In the $n$-firm oligopoly, firm $i$ sells product $i$, chooses a price $p_i\ge 0$ (equivalently $u_i\le\alpha_i$) and earns $R_i=p_i\,Q_i$. A **Nash equilibrium in prices** is a price vector $p^*\ge 0$ from which no firm can raise its revenue by changing its own price to any other nonnegative price; $u^*_i=\alpha_i-\beta p^*_i$, $Q^*_i$ and $R^*_i$ are the equilibrium ideal utilities, market shares and revenues. The ratio $\tau_i(\mathbf u)=Q_i(\mathbf u)/(\partial Q_i(\mathbf u)/\partial u_i)$ is (12), $L=\sum_{k\in N}\lambda_k$, $M=\max_{j}\alpha_j$, and for a set $S$ of solved products with values $u^*_k$, $\tau_i(u_i\mid u(S))$ is $\tau_i$ evaluated with coordinate $i$ equal to $u_i$, coordinate $k\in S$ equal to $u^*_k$, and every other coordinate equal to $M$ (13). Suppose that for any two products $i,j$, $\alpha_i+1/\lambda_i\le\alpha_j+1/\lambda_j$ implies $\alpha_i\le\alpha_j$. Relabel the products so that $\alpha_1+1/\lambda_1\le\dots\le\alpha_n+1/\lambda_n$ (ties broken arbitrarily). The procedure sets $u^*_1=\alpha_1-1/(L-\lambda_1)$, then for $i=2,\dots,n$ in turn solves $\alpha_i-u_i=\tau_i(u_i\mid u(S))$ with $S=\{1,\dots,i-1\}$ for the unique $u_i=u^*_i$, and sets $p^*_i=(\alpha_i-u^*_i)/\beta$. **Theorem 11**: for every such labeling,
--
--   1. the procedure is well defined: each equation has exactly one solution;
--   2. $\mathbf p^*$ is a Nash equilibrium in prices, and the only one;
--   3. $u^*_i\ge u^*_{i-1}$ for $i=2,\dots,n$, with equality only if $\alpha_i=\alpha_{i-1}$ and $\lambda_i=\lambda_{i-1}$.
--
--   $$
--   u^*_1\le u^*_2\le\dots\le u^*_n .
--   $$
--
--   Under this condition the equilibrium is found in a single pass, and larger $\alpha_i+1/\lambda_i$ means a larger equilibrium ideal utility.
--
--   **Formalization Note** The labeling is an order `σ : Fin n ≃ Fin n` along which $\alpha+1/\lambda$ is monotone; the theorem quantifies over every such order. `IsOnePass` is the procedure; existence of its output is part of the conclusion.
--
--   Differences from the source:
--   - encoding: "relabel all products so that α_1 + 1/λ_1 ≤ ⋯ ≤ α_n + 1/λ_n (breaking ties arbitrarily)" → every σ : Fin n ≃ Fin n with s ↦ α(σ s) + 1/λ(σ s) monotone; reason: the relabeling is the order σ; quantifying over all of them is arbitrary tie-breaking
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), pp. 31–32, Theorem 11; proof pp. 61–62

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem theorem_11 {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (hα : ∀ i j, α i + 1 / lam i ≤ α j + 1 / lam j → α i ≤ α j)
    (σ : Fin n ≃ Fin n) (hσ : Monotone (fun s => α (σ s) + 1 / lam (σ s))) :
    (∃ ustar : Fin n → ℝ, IsOnePass α lam σ ustar) ∧
      ∀ ustar : Fin n → ℝ, IsOnePass α lam σ ustar →
        (∀ s : Fin n, 0 < s.val →
            ∃! x : ℝ, α (σ s) - x = tauCond α lam (solvedBefore σ s.val) ustar (σ s) x) ∧
          IsPriceNE α β lam (eqPrices α β ustar) ∧
          (∀ p, IsPriceNE α β lam p → p = eqPrices α β ustar) ∧
          ∀ s t : Fin n, t.val + 1 = s.val →
            ustar (σ t) ≤ ustar (σ s) ∧
              (ustar (σ t) = ustar (σ s) → α (σ s) = α (σ t) ∧ lam (σ s) = lam (σ t)) := by sorry

end HetExponomial.ChoiceProb.Supplement
