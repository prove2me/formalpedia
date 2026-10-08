-- Prove2me | Theorems.Thm_HuImkellerMuller_Power_eq_14
-- name    : HuImkellerMuller.Power.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:42.522719+00:00
-- url     : https://prove2.me/theorems/16461b05-3dc2-4ce3-81ea-44c4386e8f2f
-- title:
--   (14), p. 17 — γρθ − ½γ|ρ|² + f(z) ≤ −½|γρ + z|² for ρ ∈ C, with equality on Π_C((z + θ)/(1 − γ))
-- statement:
--   Let $C\subseteq\mathbb R^m$ be closed, $\theta,z\in\mathbb R^m$ and $\gamma\in(0,1)$, and let
--   $$
--   f(z)=\frac{\gamma(1-\gamma)}{2}\operatorname{dist}^2\Big(\frac1{1-\gamma}(z+\theta),C\Big)-\frac{\gamma|z+\theta|^2}{2(1-\gamma)}-\frac12|z|^2.
--   $$
--   Then for every $\rho\in C$,
--   $$
--   \gamma\rho\theta-\tfrac12\gamma|\rho|^2+f(z)\le-\tfrac12|\gamma\rho+z|^2,
--   $$
--   and equality holds for every $\rho\in\Pi_C\big(\frac1{1-\gamma}(z+\theta)\big)$.
--
--   This is inequality (14) of the paper together with the choice of $f$ that makes it tight: it is what makes $\tilde R^{(\rho)}$ a supermartingale for every admissible $\rho$ and a martingale for a selection $\rho^*$ of the projection.
--
--   **Formalization Note** The paper states (14) along processes, at $(\theta_t,C_t(\omega),Z_t,\rho_t)$, "for all $\rho\in\tilde{\mathcal A}$". It is stated here pointwise for a fixed closed set and fixed vectors; the constraint $\rho_t\in C_t$ of $\tilde{\mathcal A}$ becomes $\rho\in C$. The products $\rho\theta$ are Euclidean inner products.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, (14) and the choice of f, p. 17

import Mathlib
import Definitions.Def_HuImkellerMuller_Power_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Power

/-- (14) and the choice of `f`, p. 17, pointwise: for a closed `C ⊆ ℝᵐ`, `θ, z ∈ ℝᵐ` and
`γ ∈ (0, 1)`, with `f(z) = powerDriver θ C γ z`, every `ρ ∈ C` satisfies
`γ ρθ − ½ γ |ρ|² + f(z) ≤ −½ |γρ + z|²`, with equality for every
`ρ ∈ Π_C((z + θ)/(1 − γ))`. -/
theorem eq_14 {m : ℕ} (C : Set (EuclideanSpace ℝ (Fin m))) (hC : IsClosed C)
    (θ z : EuclideanSpace ℝ (Fin m)) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ ρ ∈ C, γ * inner ℝ ρ θ - (1 / 2) * γ * ‖ρ‖ ^ 2 + powerDriver θ C γ z
        ≤ -(1 / 2) * ‖γ • ρ + z‖ ^ 2) ∧
    (∀ ρ ∈ HuImkellerMuller.Exponential.proj C ((1 / (1 - γ)) • (z + θ)),
        γ * inner ℝ ρ θ - (1 / 2) * γ * ‖ρ‖ ^ 2 + powerDriver θ C γ z
          = -(1 / 2) * ‖γ • ρ + z‖ ^ 2) := by sorry

end HuImkellerMuller.Power
