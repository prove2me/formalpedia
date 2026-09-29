-- Prove2me | Theorems.Thm_MonopolesInstantonsConfinement_static_first_integral_deriv_zero
-- name    : MonopolesInstantonsConfinement.static_first_integral_deriv_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:26:24.014853+00:00
-- url     : https://prove2.me/theorems/1b744821-04b6-4f60-8b2a-3f6cb6e74cd4
-- title:
--   Vanishing derivative of the static field energy
-- statement:
--   Let $V : \mathbb R \to \mathbb R$ be differentiable and $\varphi : \mathbb R \to \mathbb R$ be twice continuously differentiable satisfying the static Euler–Lagrange equation $\varphi''(x) = V'(\varphi(x))$ for all $x \in \mathbb R$. Then the spatial derivative of the static energy density $E(x) = \frac{1}{2}\varphi'(x)^2 - V(\varphi(x))$ vanishes at every point $x \in \mathbb R$:
--
--   $$ \frac{d}{dx}\left(\frac{1}{2}\varphi'(x)^2 - V(\varphi(x))\right) = 0. $$
--
--   By differentiating via the chain and product rules: $\frac{d}{dx}(\frac{1}{2}\varphi'(x)^2 - V(\varphi(x))) = \varphi'(x)\varphi''(x) - V'(\varphi(x))\varphi'(x) = \varphi'(x)(\varphi''(x) - V'(\varphi(x))) = 0$.
-- source:
--   G. 't Hooft, Monopoles, Instantons and Confinement (lecture notes by F. Bruckmann), arXiv:hep-th/0010225, Chapter 1, Section 1.2, p. 3, eq. (1.4)

import Mathlib
import Definitions.Def_MIC_kink_solitons_1d
open Filter Topology

namespace MonopolesInstantonsConfinement

theorem static_first_integral_deriv_zero (V : ℝ → ℝ) (hV : Differentiable ℝ V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hEL : ∀ x, deriv (deriv φ) x = deriv V (φ x)) (x : ℝ) :
    deriv (fun y => 1 / 2 * deriv φ y ^ 2 - V (φ y)) x = 0 := by sorry

end MonopolesInstantonsConfinement
