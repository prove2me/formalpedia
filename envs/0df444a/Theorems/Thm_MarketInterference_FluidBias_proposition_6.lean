-- Prove2me | Theorems.Thm_MarketInterference_FluidBias_proposition_6
-- name    : MarketInterference.FluidBias.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:00.919633+00:00
-- url     : https://prove2.me/theorems/3ccd254b-cc2d-43e0-b544-3fad3787a180
-- title:
--   Proposition 6, p. 21 — Ψ′(η) = a^η·β off finitely many points, and Δ = ∫₀¹ a^η·β dη
-- statement:
--   Let $\mathcal G$ be a matching network with rates $\lambda\ge0$, $\lambda+\beta\ge0$, $\pi\ge0$, and let $\Psi(\eta)=\Phi(\lambda+\eta\beta,\pi)$. For each $\eta\in[0,1]$ let $a^\eta$ be the demand part of an optimal solution of the dual (5) of $\Phi(\lambda+\eta\beta,\pi)$ (any choice when it is not unique). Then
--
--   1. $\Psi'(\eta)=a^\eta\cdot\beta$ for all but finitely many $\eta\in(0,1)$;
--   2. the global treatment effect is the integral of the shadow-price slope:
--   $$
--   \Delta=\Psi(1)-\Psi(0)=\int_0^1 a^\eta\cdot\beta\,d\eta. \tag{12}
--   $$
--
--   This fundamental-theorem-of-calculus identity expresses $\Delta$ through the marginal values $a^\eta$, which the SP estimator samples at $\eta=\rho$.
--
--   **Formalization Note.** The first conjunct is the premise "let $\Psi'(\eta)=a^\eta\cdot\beta$ designate the derivative … defined on all but finitely many points", which the page asserts; it is stated with `HasDerivAt` at every point of $(0,1)$ outside a finite set. The selection $\eta\mapsto a^\eta$ is arbitrary; no measurability hypothesis is added. No assumption on $\rho$ or the sign of $\beta$ is needed, and none is added.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 21, Proposition 6, (12); p. 20 (a^η)

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidBias_PathFlow
import Definitions.Def_MarketInterference_FluidBias_Estimators

namespace MarketInterference.FluidBias

/-- Proposition 6 (p. 21, fundamental theorem of calculus). Let `a^η` be, for each
`η ∈ [0, 1]`, the demand part of some optimal solution of the dual (5) of `Φ(λ + ηβ, π)`. Then
`η ↦ a^η · β` is the derivative of `Ψ` at every point of `(0, 1)` outside a finite set, and
`Δ = Ψ(1) − Ψ(0) = ∫₀¹ a^η · β dη`. -/
theorem proposition_6 {nd ns : ℕ} {I E : Type} [Fintype I] [DecidableEq I] [Fintype E]
    (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi)
    (a : ℝ → Fin nd → ℝ)
    (ha : ∀ η ∈ Set.Icc (0 : ℝ) 1,
      ∃ q : DualVar nd ns I E, IsOptimalDual N 1 (lam + η • beta) pi q ∧ q.a = a η) :
    (∃ F : Set ℝ, F.Finite ∧
        ∀ η ∈ Set.Ioo (0 : ℝ) 1 \ F, HasDerivAt (Psi N lam beta pi) (a η ⬝ᵥ beta) η) ∧
      Delta N lam beta pi = ∫ η in (0 : ℝ)..1, a η ⬝ᵥ beta := by sorry

end MarketInterference.FluidBias
