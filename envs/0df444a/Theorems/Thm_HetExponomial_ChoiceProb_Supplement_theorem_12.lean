-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_Supplement_theorem_12
-- name    : HetExponomial.ChoiceProb.Supplement.theorem_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:43:16.393305+00:00
-- url     : https://prove2.me/theorems/2a8f8bd6-1360-4aea-a637-99c043b7a79c
-- title:
--   Theorem 12, pp. 32–33 — symmetric cases: (a) equal λ, (b) equal α, (c) equal λ and α with p*_i = 1/[βλ(n − 1)], Q*_i = 1/n
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ with $n\ge 2$, the ideal utilities $u_i$ are real, and the errors $z_1,\dots,z_n$ are independent with $z_j\sim\mathrm{Exp}(\lambda_j)$, $\lambda_j>0$; $Q_i(\mathbf u,\boldsymbol\lambda)=P\{u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$ is the HEC choice probability. In the pricing model, product $i$ has ideal utility $u_i=\alpha_i-\beta p_i$ at price $p_i$, with intrinsic desirability $\alpha_i\in\mathbb R$ and price sensitivity $\beta>0$; market size is $1$ and marginal costs are $0$. In the $n$-firm oligopoly, firm $i$ sells product $i$, chooses a price $p_i\ge 0$ (equivalently $u_i\le\alpha_i$) and earns $R_i=p_i\,Q_i$. A **Nash equilibrium in prices** is a price vector $p^*\ge 0$ from which no firm can raise its revenue by changing its own price to any other nonnegative price; $u^*_i=\alpha_i-\beta p^*_i$, $Q^*_i$ and $R^*_i$ are the equilibrium ideal utilities, market shares and revenues. The ratio $\tau_i(\mathbf u)=Q_i(\mathbf u)/(\partial Q_i(\mathbf u)/\partial u_i)$ is (12), $L=\sum_{k\in N}\lambda_k$, $M=\max_{j}\alpha_j$, and for a set $S$ of solved products with values $u^*_k$, $\tau_i(u_i\mid u(S))$ is $\tau_i$ evaluated with coordinate $i$ equal to $u_i$, coordinate $k\in S$ equal to $u^*_k$, and every other coordinate equal to $M$ (13). **(a) Products symmetric in error distribution.** If $\lambda_i=\lambda$ for all $i$, then for every ordering with $\alpha_1\le\alpha_2\le\dots\le\alpha_n$ (ties arbitrary), solving the first-order conditions (12) one product at a time in that order (each in its conditional form (13) given the earlier products) is well defined, produces a Nash equilibrium in prices, and that equilibrium is the unique one. Moreover $p^*_1\le\dots\le p^*_n$, $Q^*_1\le\dots\le Q^*_n$ and $R^*_1\le\dots\le R^*_n$.
--
--   **(b) Products symmetric in intrinsic desirability.** If $\alpha_i=\alpha$ for all $i$, the same holds for every ordering with $\lambda_1\ge\lambda_2\ge\dots\ge\lambda_n$, and then $p^*_1\ge\dots\ge p^*_n$, $Q^*_1\ge\dots\ge Q^*_n$ and $R^*_1\ge\dots\ge R^*_n$.
--
--   **(c) Purely symmetric products.** If $\lambda_i=\lambda$ and $\alpha_i=\alpha$ for all $i$, the unique Nash equilibrium in prices is symmetric, with
--   $$
--   p^*_i=\frac{1}{\beta\lambda(n-1)},\qquad Q^*_i=\frac1n,\qquad R^*_i=\frac{1}{\beta\lambda n(n-1)}\qquad\text{for all }i.
--   $$
--
--   These symmetric cases isolate the effect of intrinsic desirability (a) and of error variability (b) on the equilibrium.
--
--   **Formalization Note** An ordering is `σ : Fin n ≃ Fin n`; monotone sequences are `Monotone`/`Antitone` along $\sigma$. "Solving (12) in that order" is `IsSequentialFOC`: every product, the first included, solves $\alpha_i-u=\tau_i(u\mid u(S))$ with $S$ the earlier products.
--
--   Differences from the source:
--   - reading: "solving (12) in that order" → IsSequentialFOC: each product in turn solves the conditional FOC (13) α_i − u = τ_i(u | u(S)) with S the earlier products; reason: (13) on p. 29 is how the paper solves (12) sequentially, and the proof (p. 62) refers to the procedure of Theorem 11
--   - encoding: "rank-ordering the products" (ties arbitrary) → every σ : Fin n ≃ Fin n along which α is monotone (a) or λ antitone (b); reason: quantifying over all orderings is arbitrary tie-breaking
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), pp. 32–33, Theorem 12; proof pp. 62–63

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model
import Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

theorem theorem_12 {n : ℕ} (hn : 2 ≤ n) (α : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) :
    -- (a) Products Symmetric in Error Distribution
    ((∃ c : ℝ, ∀ i, lam i = c) →
      ∀ σ : Fin n ≃ Fin n, Monotone (fun s => α (σ s)) →
        (∃ ustar : Fin n → ℝ, IsSequentialFOC α lam σ ustar) ∧
          ∀ ustar : Fin n → ℝ, IsSequentialFOC α lam σ ustar →
            (∀ s : Fin n,
                ∃! x : ℝ, α (σ s) - x = tauCond α lam (solvedBefore σ s.val) ustar (σ s) x) ∧
              IsPriceNE α β lam (eqPrices α β ustar) ∧
              (∀ p, IsPriceNE α β lam p → p = eqPrices α β ustar) ∧
              Monotone (fun s => eqPrices α β ustar (σ s)) ∧
              Monotone (fun s => choiceProb (util α β (eqPrices α β ustar)) lam (σ s)) ∧
              Monotone (fun s => firmRevenue α β lam (eqPrices α β ustar) (σ s))) ∧
    -- (b) Products Symmetric in Intrinsic Desirability
    ((∃ a : ℝ, ∀ i, α i = a) →
      ∀ σ : Fin n ≃ Fin n, Antitone (fun s => lam (σ s)) →
        (∃ ustar : Fin n → ℝ, IsSequentialFOC α lam σ ustar) ∧
          ∀ ustar : Fin n → ℝ, IsSequentialFOC α lam σ ustar →
            (∀ s : Fin n,
                ∃! x : ℝ, α (σ s) - x = tauCond α lam (solvedBefore σ s.val) ustar (σ s) x) ∧
              IsPriceNE α β lam (eqPrices α β ustar) ∧
              (∀ p, IsPriceNE α β lam p → p = eqPrices α β ustar) ∧
              Antitone (fun s => eqPrices α β ustar (σ s)) ∧
              Antitone (fun s => choiceProb (util α β (eqPrices α β ustar)) lam (σ s)) ∧
              Antitone (fun s => firmRevenue α β lam (eqPrices α β ustar) (σ s))) ∧
    -- (c) Purely Symmetric Products
    (∀ c a : ℝ, (∀ i, lam i = c) → (∀ i, α i = a) →
      IsPriceNE α β lam (fun _ => 1 / (β * c * ((n : ℝ) - 1))) ∧
        (∀ p, IsPriceNE α β lam p → p = fun _ => 1 / (β * c * ((n : ℝ) - 1))) ∧
        ∀ i, choiceProb (util α β (fun _ => 1 / (β * c * ((n : ℝ) - 1)))) lam i = 1 / n ∧
          firmRevenue α β lam (fun _ => 1 / (β * c * ((n : ℝ) - 1))) i =
            1 / (β * c * n * ((n : ℝ) - 1))) := by sorry

end HetExponomial.ChoiceProb.Supplement
