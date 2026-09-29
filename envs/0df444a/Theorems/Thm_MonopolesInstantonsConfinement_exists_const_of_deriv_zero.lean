-- Prove2me | Theorems.Thm_MonopolesInstantonsConfinement_exists_const_of_deriv_zero
-- name    : MonopolesInstantonsConfinement.exists_const_of_deriv_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:26:15.009004+00:00
-- url     : https://prove2.me/theorems/61f6fb45-c2bd-4a9c-9b98-30f3e3179ed3
-- title:
--   Constancy from vanishing derivative of static energy
-- statement:
--   Let $V : \mathbb R \to \mathbb R$ be differentiable and $\varphi : \mathbb R \to \mathbb R$ be $C^2$. If the derivative of $E(x) = \frac{1}{2}\varphi'(x)^2 - V(\varphi(x))$ vanishes everywhere on $\mathbb R$, then there exists a constant $c \in \mathbb R$ such that $E(x) = c$ for all $x \in \mathbb R$. This follows from the mean value theorem on $\mathbb R$.
-- source:
--   G. 't Hooft, Monopoles, Instantons and Confinement (lecture notes by F. Bruckmann), arXiv:hep-th/0010225, Chapter 1, Section 1.2, p. 3, eq. (1.4)

import Mathlib
import Definitions.Def_MIC_kink_solitons_1d
open Filter Topology

namespace MonopolesInstantonsConfinement

theorem exists_const_of_deriv_zero (V : ℝ → ℝ) (hV : Differentiable ℝ V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hderiv : ∀ x, deriv (fun y => 1 / 2 * deriv φ y ^ 2 - V (φ y)) x = 0) :
    ∃ c : ℝ, ∀ x, 1 / 2 * deriv φ x ^ 2 - V (φ x) = c := by sorry

end MonopolesInstantonsConfinement
