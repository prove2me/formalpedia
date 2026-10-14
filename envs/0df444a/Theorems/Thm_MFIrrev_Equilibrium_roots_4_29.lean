-- Prove2me | Theorems.Thm_MFIrrev_Equilibrium_roots_4_29
-- name    : MFIrrev.Equilibrium.roots_4_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:20.415969+00:00
-- url     : https://prove2.me/theorems/51af128f-3de8-4503-8e39-5b988da832de
-- title:
--   (4.29), p. 21 — ϕ̄(θ) = ϕ₁(θ)ϕ₂(θ) − p₁p₂ has exactly four real roots θ₁ < θ₂ < θ₃ = 0 < θ₄, and θ₁ < α₁⁻ < θ₂
-- statement:
--   Let $\delta>0$, $\sigma_1,\sigma_2>0$ and $p_1,p_2\in(0,1)$, and let
--   $$\phi_i(\theta)=\tfrac12\sigma_i^2\theta^2+\big(\delta+\tfrac12\sigma_i^2\big)\theta-p_i,\qquad \bar\phi(\theta)=\phi_1(\theta)\phi_2(\theta)-p_1p_2.$$
--   Then there are reals $\theta_1<\theta_2<0<\theta_4$ such that the real roots of $\bar\phi$ are exactly
--   $$\theta_1<\theta_2<\theta_3=0<\theta_4.$$
--   Moreover the negative root $\alpha_1^-$ of $\phi_1$ (4.28) satisfies $\theta_1<\alpha_1^-<\theta_2$.
--
--   The two negative roots $\theta_1,\theta_2$ are the exponents of the tail of the stationary distribution of the equilibrium capacity; the condition $1+\theta_2<0$ of Theorem 4.1 is a condition on the larger one.
--
--   **Formalization Note.** The ordering $\theta_1<\alpha_1^-<\theta_2$ is not on p. 21; it is the corrected form of (A.18), p. 29, which prints $\theta_1<\theta_2<\alpha_2<0$ (with $\alpha_2=\alpha_1^-$). Since $\bar\phi(\alpha_1^-)=-p_1p_2<0$ while $\bar\phi>0$ just left of $0$, $\alpha_1^-$ lies between the two negative roots. It guarantees that (4.35) never divides by zero when $1+\theta_2<0$.
-- source:
--   Aïd, Basei & Ferrari, A Stationary Mean-Field Equilibrium Model of Irreversible Investment in a Two-Regime Economy, arXiv:2305.00541v1, p. 21, (4.27)–(4.29) and the paragraph after (4.30); ordering: corrected (A.18), p. 29

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_Analytic

namespace MFIrrev.Equilibrium

/-- The roots of (4.29), Aïd–Basei–Ferrari p. 21: `ϕ̄(θ) = ϕ₁(θ)ϕ₂(θ) − p₁p₂` has exactly the four real
roots `θ₁ < θ₂ < θ₃ = 0 < θ₄`. In addition (corrected (A.18), p. 29) the negative root `α₁⁻` of
`ϕ₁` lies strictly between `θ₁` and `θ₂`. -/
theorem roots_4_29 (m : Params) (hδ : 0 < m.δ) (hσ : ∀ j, 0 < m.σ j)
    (hp : ∀ j, 0 < m.p j ∧ m.p j < 1) :
    ∃ θ1 θ2 θ4 : ℝ, θ1 < θ2 ∧ θ2 < 0 ∧ 0 < θ4 ∧
      (∀ θ : ℝ, phiBar m θ = 0 ↔ θ = θ1 ∨ θ = θ2 ∨ θ = 0 ∨ θ = θ4) ∧
      θ1 < alphaMinus m ∧ alphaMinus m < θ2 := by sorry

end MFIrrev.Equilibrium
