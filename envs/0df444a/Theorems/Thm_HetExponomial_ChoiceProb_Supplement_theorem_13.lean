-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_theorem_13
-- name    : HetExponomial.ChoiceProb.Supplement.theorem_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:43:58.759113+00:00
-- url     : https://prove2.me/theorems/28b1f30a-74a3-46a9-9408-e51370649a1f
-- title:
--   Theorem 13, p. 40 — under α_i + 1/λ_i ≤ α_j + 1/λ_j ⇒ α_i ≤ α_j ∧ λ_i ≤ λ_j, the Theorem 11 procedure gives the unique NE with p*, Q*, R* nondecreasing
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. In the pricing model, product $i$ has ideal utility $u_i=\alpha_i-\beta p_i$ at price $p_i$, with intrinsic desirability $\alpha_i\in\mathbb R$ and price sensitivity $\beta>0$; market size is $1$ and marginal costs are $0$. In the $n$-firm oligopoly, firm $i$ sells product $i$, chooses a price $p_i\ge 0$ (equivalently $u_i\le\alpha_i$) and earns $R_i=p_i\,Q_i$. A **Nash equilibrium in prices** is a price vector $p^*\ge 0$ from which no firm can raise its revenue by changing its own price to any other nonnegative price; $u^*_i=\alpha_i-\beta p^*_i$, $Q^*_i$ and $R^*_i$ are the equilibrium ideal utilities, market shares and revenues. The ratio $\tau_i(\mathbf u)=Q_i(\mathbf u)/(\partial Q_i(\mathbf u)/\partial u_i)$ is (12), $L=\sum_{k\in N}\lambda_k$, $M=\max_{j}\alpha_j$, and for a set $S$ of solved products with values $u^*_k$, $\tau_i(u_i\mid u(S))$ is $\tau_i$ evaluated with coordinate $i$ equal to $u_i$, coordinate $k\in S$ equal to $u^*_k$, and every other coordinate equal to $M$ (13). Suppose that for any two products $i,j$, $\alpha_i+1/\lambda_i\le\alpha_j+1/\lambda_j$ implies $\alpha_i\le\alpha_j$ and $\lambda_i\le\lambda_j$. Then for every labeling with $\alpha_1+1/\lambda_1\le\dots\le\alpha_n+1/\lambda_n$ (ties arbitrary), the one-pass procedure of Theorem 11 is well defined and produces a Nash equilibrium in prices, which is the unique one, and
--   $$
--   p^*_1\le\dots\le p^*_n,\qquad Q^*_1\le\dots\le Q^*_n,\qquad R^*_1\le\dots\le R^*_n .
--   $$
--
--   This is the "total dominance" case: a product that is better in both intrinsic desirability and error variability gets a higher price, share and revenue in equilibrium.
--
--   **Formalization Note** The labeling is an order `σ : Fin n ≃ Fin n`; the procedure is `IsOnePass`, as in Theorem 11.
--
--   Differences from the source:
--   - encoding: "relabeling all products so that α_1 + 1/λ_1 ≤ ⋯ ≤ α_n + 1/λ_n (breaking ties arbitrarily)" → every σ : Fin n ≃ Fin n with s ↦ α(σ s) + 1/λ(σ s) monotone; reason: quantifying over all such orders is arbitrary tie-breaking
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 40, Theorem 13 (Appendix A); proof p. 63

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem theorem_13 {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (hα : ∀ i j, α i + 1 / lam i ≤ α j + 1 / lam j → α i ≤ α j ∧ lam i ≤ lam j)
    (σ : Fin n ≃ Fin n) (hσ : Monotone (fun s => α (σ s) + 1 / lam (σ s))) :
    (∃ ustar : Fin n → ℝ, IsOnePass α lam σ ustar) ∧
      ∀ ustar : Fin n → ℝ, IsOnePass α lam σ ustar →
        (∀ s : Fin n, 0 < s.val →
            ∃! x : ℝ, α (σ s) - x = tauCond α lam (solvedBefore σ s.val) ustar (σ s) x) ∧
          IsPriceNE α β lam (eqPrices α β ustar) ∧
          (∀ p, IsPriceNE α β lam p → p = eqPrices α β ustar) ∧
          Monotone (fun s => eqPrices α β ustar (σ s)) ∧
          Monotone (fun s => choiceProb (util α β (eqPrices α β ustar)) lam (σ s)) ∧
          Monotone (fun s => firmRevenue α β lam (eqPrices α β ustar) (σ s)) := by sorry

end HetExponomial.ChoiceProb.Supplement
