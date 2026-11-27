-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_theorem_14
-- name    : HetExponomial.ChoiceProb.Supplement.theorem_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:44:51.93617+00:00
-- url     : https://prove2.me/theorems/93401c67-5a49-4dae-ac6b-89ba30b54ecd
-- title:
--   Theorem 14, pp. 40–41 — duopoly with α_1 + 1/λ_1 ≤ α_2 + 1/λ_2: unique NE (1/(βλ_2), p̂_2), bounds, closed-form shares and revenues, comparisons
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. In the pricing model, product $i$ has ideal utility $u_i=\alpha_i-\beta p_i$ at price $p_i$, with intrinsic desirability $\alpha_i\in\mathbb R$ and price sensitivity $\beta>0$; market size is $1$ and marginal costs are $0$. In the $n$-firm oligopoly, firm $i$ sells product $i$, chooses a price $p_i\ge 0$ (equivalently $u_i\le\alpha_i$) and earns $R_i=p_i\,Q_i$. A **Nash equilibrium in prices** is a price vector $p^*\ge 0$ from which no firm can raise its revenue by changing its own price to any other nonnegative price; $u^*_i=\alpha_i-\beta p^*_i$, $Q^*_i$ and $R^*_i$ are the equilibrium ideal utilities, market shares and revenues. The ratio $\tau_i(\mathbf u)=Q_i(\mathbf u)/(\partial Q_i(\mathbf u)/\partial u_i)$ is (12), $L=\sum_{k\in N}\lambda_k$, $M=\max_{j}\alpha_j$, and for a set $S$ of solved products with values $u^*_k$, $\tau_i(u_i\mid u(S))$ is $\tau_i$ evaluated with coordinate $i$ equal to $u_i$, coordinate $k\in S$ equal to $u^*_k$, and every other coordinate equal to $M$ (13). Let $n=2$ and $\alpha_1+1/\lambda_1\le\alpha_2+1/\lambda_2$. Then:
--
--   1. the equation
--   $$
--   \beta\lambda_2\hat p_2=1+\lambda_2(\alpha_2-\alpha_1)-\ln\Big(\frac{\lambda_1+\beta\lambda_1\lambda_2\hat p_2}{\lambda_1+\lambda_2}\Big)
--   $$
--   has exactly one solution $\hat p_2$ (among the $\hat p_2$ for which the logarithm's argument is positive), and it satisfies $1/(\beta\lambda_1)\le\hat p_2\le 1/(\beta\lambda_2)+(\alpha_2-\alpha_1)/\beta$;
--   2. the unique Nash equilibrium in prices is $(p^*_1,p^*_2)=(1/(\beta\lambda_2),\hat p_2)$;
--   3. the equilibrium shares and revenues are
--   $$
--   Q^*_1=\frac{\lambda_1}{\lambda_1+\beta\lambda_1\lambda_2\hat p_2},\quad R^*_1=\frac{1}{\beta\lambda_2}\cdot\frac{\lambda_1}{\lambda_1+\beta\lambda_1\lambda_2\hat p_2},\quad Q^*_2=\frac{\beta\lambda_1\lambda_2\hat p_2}{\lambda_1+\beta\lambda_1\lambda_2\hat p_2},\quad R^*_2=\frac{\beta\lambda_1\lambda_2\hat p_2^{\,2}}{\lambda_1+\beta\lambda_1\lambda_2\hat p_2};
--   $$
--   4. $u^*_1\le u^*_2$, $p^*_2Q^*_1=p^*_1Q^*_2$, and $R^*_1\ge R^*_2\iff p^*_1\ge p^*_2\iff Q^*_1\ge Q^*_2$.
--
--   The duopoly is solved in closed form up to one scalar equation, and the ranking of equilibrium ideal utilities follows $\alpha_i+1/\lambda_i$ without further conditions.
--
--   **Formalization Note** Products 1 and 2 are indices `0` and `1` of `Fin 2`; the price vector is `![1 / (β * lam 1), p₂]`. Every clause is stated for each solution $\hat p_2$ of the equation in the domain $\lambda_1+\beta\lambda_1\lambda_2\hat p_2>0$, and the first clause asserts that there is exactly one.
--
--   Differences from the source:
--   - encoding: products 1, 2 → indices 0, 1 of Fin 2; reason: Lean convention; the same instances
--   - reading: "p̂_2 is the unique solution of βλ_2p̂_2 = 1 + λ_2(α_2 − α_1) − ln((λ_1 + βλ_1λ_2p̂_2)/(λ_1 + λ_2))" → unique among p₂ with λ_1 + βλ_1λ_2 p₂ > 0; reason: ln is defined only for a positive argument; Lean's Real.log is |·|-symmetric and 0 at 0, which would admit spurious roots outside the domain
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), pp. 40–41, Theorem 14 (Appendix A); proof pp. 63–64

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem theorem_14 (α : Fin 2 → ℝ) (β : ℝ) (hβ : 0 < β) (lam : Fin 2 → ℝ)
    (hlam : ∀ j, 0 < lam j) (h12 : α 0 + 1 / lam 0 ≤ α 1 + 1 / lam 1) :
    (∃! p₂ : ℝ, 0 < lam 0 + β * lam 0 * lam 1 * p₂ ∧
        β * lam 1 * p₂ = 1 + lam 1 * (α 1 - α 0) -
          Real.log ((lam 0 + β * lam 0 * lam 1 * p₂) / (lam 0 + lam 1))) ∧
      ∀ p₂ : ℝ, 0 < lam 0 + β * lam 0 * lam 1 * p₂ →
        β * lam 1 * p₂ = 1 + lam 1 * (α 1 - α 0) -
          Real.log ((lam 0 + β * lam 0 * lam 1 * p₂) / (lam 0 + lam 1)) →
        -- the bounds on p̂₂
        (1 / (β * lam 0) ≤ p₂ ∧ p₂ ≤ 1 / (β * lam 1) + (α 1 - α 0) / β) ∧
        -- the unique Nash equilibrium
        IsPriceNE α β lam ![1 / (β * lam 1), p₂] ∧
        (∀ p, IsPriceNE α β lam p → p = ![1 / (β * lam 1), p₂]) ∧
        -- market shares and revenues
        choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 0 =
          lam 0 / (lam 0 + β * lam 0 * lam 1 * p₂) ∧
        firmRevenue α β lam ![1 / (β * lam 1), p₂] 0 =
          1 / (β * lam 1) * (lam 0 / (lam 0 + β * lam 0 * lam 1 * p₂)) ∧
        choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 1 =
          β * lam 0 * lam 1 * p₂ / (lam 0 + β * lam 0 * lam 1 * p₂) ∧
        firmRevenue α β lam ![1 / (β * lam 1), p₂] 1 =
          β * lam 0 * lam 1 * p₂ ^ 2 / (lam 0 + β * lam 0 * lam 1 * p₂) ∧
        -- the final comparisons
        util α β ![1 / (β * lam 1), p₂] 0 ≤ util α β ![1 / (β * lam 1), p₂] 1 ∧
        p₂ * choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 0 =
          1 / (β * lam 1) * choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 1 ∧
        (firmRevenue α β lam ![1 / (β * lam 1), p₂] 1 ≤
            firmRevenue α β lam ![1 / (β * lam 1), p₂] 0 ↔ p₂ ≤ 1 / (β * lam 1)) ∧
        (p₂ ≤ 1 / (β * lam 1) ↔
          choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 1 ≤
            choiceProb (util α β ![1 / (β * lam 1), p₂]) lam 0) := by sorry

end HetExponomial.ChoiceProb.Supplement
