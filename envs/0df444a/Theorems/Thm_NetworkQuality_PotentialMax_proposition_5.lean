-- Prove2me | Theorems.Thm_NetworkQuality_PotentialMax_proposition_5
-- name    : NetworkQuality.PotentialMax.proposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:11.558004+00:00
-- url     : https://prove2.me/theorems/5885a945-e8c5-4cc3-95b2-581c9c3a6259
-- title:
--   Proposition 5, p. 15 — under potential maximization the equilibrium quality satisfies c′(q) = n((1/n)Σ1/vᵢ)⁻¹(1/n)Σ∂f(i,q)/∂q
-- statement:
--   Consider the network market under the standing assumptions, with strong network effects at every quality $q\ge 0$. The firm chooses a price $p\ge 0$ and a quality $q\ge 0$ and anticipates that stage 2 plays the potential maximizer, so its profit is $\Pi(p,q)=np-c(q)$ if all consumers buying maximizes the potential $\Phi(\cdot,p,q)$ and $-c(q)$ otherwise.
--
--   Let $(p^*,q^*)$ maximize $\Pi$ over all $p\ge 0$, $q\ge 0$, with an interior quality $q^*>0$. Then the equilibrium quality $q^*$ satisfies
--   $$c'(q^*)=n\Big(\frac1n\sum_{i=1}^n\frac1{v_i}\Big)^{-1}\frac1n\sum_{i=1}^n\frac{\partial f(i,q^*)}{\partial q}.$$
--
--   The firm values quality through the harmonic mean of all consumers' valuations and the marginal benefit averaged uniformly over every possible number of buyers, rather than through the marginal consumer's valuation $v_n$ and the equilibrium benefit $f(n,q)$ alone (the Spence logic under typical selection criteria).
--
--   **Formalization Note** The paper's "equilibrium quality" is the quality component of an optimum $(p^*,q^*)$ of the firm's two-variable problem; the profit is defined through the potential-maximization selection, not through the reduced formula (14). The equation is a first-order condition, so the interior-quality hypothesis $q^*>0$ is added. The paper's "sufficiently convex" cost, which only makes the first-order condition sufficient, is not assumed: the statement is the necessary condition. Strong network effects are assumed at every $q\ge 0$ because the firm optimizes over all qualities. Derivatives are Lean's `deriv`; the standing assumptions make $c$ and each $f(i,\cdot)$ differentiable at $q^*>0$.
-- source:
--   Chan, Quality Strategies in Network Markets, SSRN 4203818 (version of April 2023), p. 15, Proposition 5

import Mathlib
import Definitions.Def_NetworkQuality_PotentialMax_Setting

namespace NetworkQuality.PotentialMax

open Market

theorem proposition_5 {n : ℕ} (M : Market n) (hM : M.Standing)
    (hstrong : ∀ q : ℝ, 0 ≤ q → M.StrongNE q)
    (pstar qstar : ℝ) (hp : 0 ≤ pstar) (hq : 0 < qstar)
    (hopt : ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → M.profitPM p q ≤ M.profitPM pstar qstar) :
    deriv M.c qstar =
      (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, 1 / M.v i)⁻¹ *
        ((1 / (n : ℝ)) * ∑ i : Fin n, deriv (M.f (i.val + 1)) qstar) := by sorry

end NetworkQuality.PotentialMax
