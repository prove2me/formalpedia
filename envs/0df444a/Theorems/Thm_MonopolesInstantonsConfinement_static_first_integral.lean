-- Prove2me | Theorems.Thm_MonopolesInstantonsConfinement_static_first_integral
-- name    : MonopolesInstantonsConfinement.static_first_integral
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:19:59.045454+00:00
-- url     : https://prove2.me/theorems/146d9066-193a-46a0-b6d9-77a802a7e72b
-- title:
--   First integral of the static field equation
-- statement:
--   Let $V : \mathbb R \to \mathbb R$ be differentiable and let $\varphi : \mathbb R \to \mathbb R$ be twice continuously differentiable and solve the static Euler–Lagrange equation
--   $$\varphi''(x) = V'(\varphi(x)) \quad \text{for all } x \in \mathbb R.$$
--   Then there is a constant $c \in \mathbb R$ such that
--   $$\tfrac12\,\varphi'(x)^2 - V(\varphi(x)) = c \quad \text{for all } x \in \mathbb R.$$
--
--   This is the mechanical "energy conservation" first integral (1.4) of the notes, obtained by viewing $x$ as time and $\varphi$ as the position of a particle in the potential $-V$; for finite-energy configurations the constant vanishes, which reduces the static equation to a first-order equation.
-- source:
--   G. 't Hooft, Monopoles, Instantons and Confinement (lecture notes by F. Bruckmann), arXiv:hep-th/0010225, https://arxiv.org/abs/hep-th/0010225, Chapter 1, Section 1.2, p. 3, eq. (1.4)

import Mathlib
import Definitions.Def_MIC_kink_solitons_1d
open Filter Topology

namespace MonopolesInstantonsConfinement

theorem static_first_integral (V : ℝ → ℝ) (hV : Differentiable ℝ V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hEL : ∀ x, deriv (deriv φ) x = deriv V (φ x)) :
    ∃ c : ℝ, ∀ x, 1 / 2 * deriv φ x ^ 2 - V (φ x) = c := by sorry

end MonopolesInstantonsConfinement
