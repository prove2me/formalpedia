-- Prove2me | Theorems.Thm_MonopolesInstantonsConfinement_kink_mass_bogomolnyi
-- name    : MonopolesInstantonsConfinement.kink_mass_bogomolnyi
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:27:23.296149+00:00
-- url     : https://prove2.me/theorems/66fbff9f-6eb6-4743-9fd8-def18f1cb6ca
-- title:
--   Kinks are energy minimisers with masses $2m^3/\lambda$ and $8m^3/\lambda$
-- statement:
--   Let $\lambda > 0$, $A > 0$, $F > 0$ and $x_0 \in \mathbb R$.
--
--   1. **Case (a).** With $m = \sqrt{\lambda F^2/3}$, $V_a(\varphi) = \frac{\lambda}{24}(\varphi^2 - F^2)^2$ and the kink $\varphi_a(x) = F\tanh\big(\frac12 m(x - x_0)\big)$,
--   $$E_{V_a}[\varphi_a] = \frac{2m^3}{\lambda}, \qquad E_{V_a}[\varphi_a] \le E_{V_a}[\varphi]$$
--   for every differentiable $\varphi : \mathbb R \to \mathbb R$ with $\varphi(-\infty) = -F$ and $\varphi(+\infty) = F$.
--   2. **Case (b).** With $m = 2\pi\sqrt A/F$, $\lambda_b = 16\pi^4 A/F^4$, $V_b(\varphi) = A\big(1 - \cos\frac{2\pi\varphi}{F}\big)$ and the soliton $\varphi_b(x) = \frac{2F}{\pi}\arctan\big(e^{m(x - x_0)}\big)$,
--   $$E_{V_b}[\varphi_b] = \frac{8m^3}{\lambda_b}, \qquad E_{V_b}[\varphi_b] \le E_{V_b}[\varphi]$$
--   for every differentiable $\varphi : \mathbb R \to \mathbb R$ with $\varphi(-\infty) = 0$ and $\varphi(+\infty) = F$.
--
--   Here $E_V[\varphi] = \int_{\mathbb R}\big(\frac12\varphi'^2 + V(\varphi)\big)dx \in [0,\infty]$ is the static energy (1.5). The theorem states that in each model the explicit soliton saturates the Bogomol'nyi bound: it is a global minimiser of the energy in its topological sector, and its mass is the one computed on p. 5 of the notes.
--
--   **Formalization Note** Limits at $\pm\infty$ are Mathlib's `atBot`/`atTop` filter limits; energies live in `ENNReal`.
-- source:
--   G. 't Hooft, Monopoles, Instantons and Confinement (lecture notes by F. Bruckmann), arXiv:hep-th/0010225, https://arxiv.org/abs/hep-th/0010225, Chapter 1, Section 1.2, p. 5 (soliton masses, eq. (1.7)) with Chapter 7, Exercise (i), p. 66

import Mathlib
import Definitions.Def_MIC_kink_solitons_1d
open Filter Topology

namespace MonopolesInstantonsConfinement

theorem kink_mass_bogomolnyi (lam A F x₀ : ℝ) (hlam : 0 < lam) (hA : 0 < A) (hF : 0 < F) :
    (staticEnergy (phi4Potential lam F) (phi4Kink lam F x₀) =
        ENNReal.ofReal (2 * phi4Mass lam F ^ 3 / lam) ∧
      ∀ φ : ℝ → ℝ, Differentiable ℝ φ →
        Tendsto φ atBot (𝓝 (-F)) → Tendsto φ atTop (𝓝 F) →
        staticEnergy (phi4Potential lam F) (phi4Kink lam F x₀) ≤
          staticEnergy (phi4Potential lam F) φ) ∧
    (staticEnergy (sineGordonPotential A F) (sineGordonKink A F x₀) =
        ENNReal.ofReal (8 * sineGordonMass A F ^ 3 / sineGordonCoupling A F) ∧
      ∀ φ : ℝ → ℝ, Differentiable ℝ φ →
        Tendsto φ atBot (𝓝 0) → Tendsto φ atTop (𝓝 F) →
        staticEnergy (sineGordonPotential A F) (sineGordonKink A F x₀) ≤
          staticEnergy (sineGordonPotential A F) φ) := by sorry

end MonopolesInstantonsConfinement
