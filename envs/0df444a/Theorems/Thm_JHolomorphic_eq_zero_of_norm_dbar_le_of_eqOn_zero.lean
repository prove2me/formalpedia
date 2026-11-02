-- Prove2me | Theorems.Thm_JHolomorphic_eq_zero_of_norm_dbar_le_of_eqOn_zero
-- name    : JHolomorphic.eq_zero_of_norm_dbar_le_of_eqOn_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T11:08:15.635423+00:00
-- url     : https://prove2.me/theorems/c58d2503-0f6a-4f8c-9565-e5800a71b5db
-- title:
--   Unique continuation for a Cauchy–Riemann inequality on the plane
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $\bar J:\mathbb{C}\to\operatorname{End}_{\mathbb{R}}(E)$ a smooth map with $\bar J(z)^2=-\mathrm{id}$ for all $z$, and $h:\mathbb{C}\to E$ a smooth map. Suppose that every $z_0\in\mathbb{C}$ has a disc $B(z_0,\rho)$, $\rho>0$, and a constant $M$ with $$\|\partial_s h(z)+\bar J(z)\,\partial_t h(z)\|\le M\,\|h(z)\|\qquad (z\in B(z_0,\rho)).$$ If $h$ vanishes on a nonempty open set, then $h\equiv0$ on $\mathbb{C}$.
--
--   This is a global unique continuation principle for solutions of linear Cauchy–Riemann type differential inequalities on the plane; it applies to derivatives and sections built from pseudoholomorphic curves.
--
--   **Formalization Note** $\partial_s h(z)$ and $\partial_t h(z)$ are `fderiv ℝ h z 1` and `fderiv ℝ h z Complex.I`; $\bar J$ takes values in `E →L[ℝ] E`.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 (case of planes)

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace JHolomorphic

open Metric Filter Topology
open scoped ContDiff

/-- A smooth `h : ℂ → E` satisfying, near every point, `‖∂ₛh + J̄(z) ∂ₜh‖ ≤ M ‖h‖` for a smooth
complex structure `J̄`, and vanishing on a nonempty open set, vanishes identically. -/
theorem eq_zero_of_norm_dbar_le_of_eqOn_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Jbar : ℂ → E →L[ℝ] E)
    (hJbar : ContDiff ℝ ∞ Jbar)
    (hJbar2 : ∀ z, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (h : ℂ → E) (hh : ContDiff ℝ ∞ h)
    (hM : ∀ z₀ : ℂ, ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I)‖ ≤ M * ‖h z‖)
    (U : Set ℂ) (hU : IsOpen U) (hne : U.Nonempty) (h0 : ∀ z ∈ U, h z = 0) :
    ∀ z, h z = 0 := by
  sorry

end JHolomorphic
