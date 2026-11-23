-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_theorem_9
-- name    : HetExponomial.ChoiceProb.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:40:28.84407+00:00
-- url     : https://prove2.me/theorems/0f191b49-7745-4bcd-a37a-f136b8639d0b
-- title:
--   Theorem 9, p. 27 — the n-firm HEC price game has a unique Nash equilibrium
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. In the pricing model, product $i$ has ideal utility $u_i=\alpha_i-\beta p_i$ at price $p_i$, with intrinsic desirability $\alpha_i\in\mathbb R$ and price sensitivity $\beta>0$; market size is $1$ and marginal costs are $0$. In the $n$-firm oligopoly, firm $i$ sells product $i$, chooses a price $p_i\ge 0$ (equivalently $u_i\le\alpha_i$) and earns $R_i=p_i\,Q_i$. A **Nash equilibrium in prices** is a price vector $p^*\ge 0$ from which no firm can raise its revenue by changing its own price to any other nonnegative price; $u^*_i=\alpha_i-\beta p^*_i$, $Q^*_i$ and $R^*_i$ are the equilibrium ideal utilities, market shares and revenues. The ratio $\tau_i(\mathbf u)=Q_i(\mathbf u)/(\partial Q_i(\mathbf u)/\partial u_i)$ is (12), $L=\sum_{k\in N}\lambda_k$, $M=\max_{j}\alpha_j$, and for a set $S$ of solved products with values $u^*_k$, $\tau_i(u_i\mid u(S))$ is $\tau_i$ evaluated with coordinate $i$ equal to $u_i$, coordinate $k\in S$ equal to $u^*_k$, and every other coordinate equal to $M$ (13). **Theorem 9**: there exists exactly one Nash equilibrium in prices,
--   $$
--   \exists!\,\mathbf p^*\in\mathbb R^n:\ \mathbf p^*\text{ is a Nash equilibrium in prices}.
--   $$
--
--   Existence and uniqueness make the equilibrium a well-defined object, which the algorithms of Theorems 10–13 then compute.
--
--   **Formalization Note** Strategies are the nonnegative prices $p_i\ge 0$, as on p. 27.
--
--   Differences from the source: none.
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 27, Theorem 9; proof pp. 57–58

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem theorem_9 {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) :
    ∃! p : Fin n → ℝ, IsPriceNE α β lam p := by sorry

end HetExponomial.ChoiceProb.Supplement
