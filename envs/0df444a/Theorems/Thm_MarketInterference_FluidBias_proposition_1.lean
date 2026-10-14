-- Prove2me | Theorems.Thm_MarketInterference_FluidBias_proposition_1
-- name    : MarketInterference.FluidBias.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:58.10654+00:00
-- url     : https://prove2.me/theorems/ad6a42ba-35a5-4489-99c6-d370a2df5eef
-- title:
--   Proposition 1, p. 13 — Ψ is concave and piecewise linear with finitely many pieces on [0, 1]
-- statement:
--   Let $\mathcal G$ be a matching network, $\lambda\ge0$ and $\lambda+\beta\ge0$ demand rates and $\pi\ge0$ a supply rate, and let $\Psi(\eta)=\Phi(\lambda+\eta\beta,\pi)$ be the partial-treatment value function. Then over $[0,1]$:
--
--   1. $\Psi$ is concave;
--   2. $\Psi$ is piecewise linear with finitely many pieces: there are breakpoints $0=t_0<t_1<\dots<t_n=1$ and constants $c_{0,k},c_{1,k}$ such that
--   $$
--   \Psi(\eta)=c_{0,k}+c_{1,k}\,\eta\qquad\text{for all }\eta\in[t_k,t_{k+1}],\ k=0,\dots,n-1.
--   $$
--
--   Concavity is what makes the RCT estimator's linear extrapolation biased, and the finitely many linear pieces make the derivative $\Psi'$ exist off finitely many points (Proposition 6).
--
--   **Formalization Note.** No assumption on $\rho$, uniqueness or the sign of $\beta$ is needed, and none is added. The finitely many pieces are encoded by a strictly increasing finite list of breakpoints from $0$ to $1$.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 13, Proposition 1 (proof p. 40)

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidBias_PathFlow
import Definitions.Def_MarketInterference_FluidBias_Estimators

namespace MarketInterference.FluidBias

/-- Proposition 1 (p. 13). Over `[0, 1]` the partial-treatment value function
`Ψ(η) = Φ(λ + ηβ, π)` is concave and piecewise linear with finitely many pieces: there are
breakpoints `0 = t₀ < t₁ < ⋯ < tₙ = 1` such that `Ψ` is affine on each `[t_k, t_{k+1}]`. -/
theorem proposition_1 {nd ns : ℕ} {I E : Type} [Fintype I] [DecidableEq I] [Fintype E]
    (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi) :
    ConcaveOn ℝ (Set.Icc 0 1) (Psi N lam beta pi) ∧
      ∃ (n : ℕ) (t : Fin (n + 1) → ℝ), t 0 = 0 ∧ t (Fin.last n) = 1 ∧ StrictMono t ∧
        ∀ k : Fin n, ∃ c₀ c₁ : ℝ, ∀ η ∈ Set.Icc (t k.castSucc) (t k.succ),
          Psi N lam beta pi η = c₀ + c₁ * η := by sorry

end MarketInterference.FluidBias
