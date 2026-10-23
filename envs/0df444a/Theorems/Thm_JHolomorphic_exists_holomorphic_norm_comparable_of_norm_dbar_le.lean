-- Prove2me | Theorems.Thm_JHolomorphic_exists_holomorphic_norm_comparable_of_norm_dbar_le
-- name    : JHolomorphic.exists_holomorphic_norm_comparable_of_norm_dbar_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T14:43:46.480413+00:00
-- url     : https://prove2.me/theorems/c40171ea-1da8-4aac-af98-cc43e51ea803
-- title:
--   Solutions of a linear Cauchy-Riemann inequality are comparable to holomorphic maps
-- statement:
--   Let $E$ be a real normed vector space of finite dimension $2n$, and let $D$ be the open unit disc in $\mathbb{C}$. Let $\bar J:D\to\mathrm{End}_{\mathbb{R}}(E)$ be $C^\infty$ with $\bar J(z)^2=-\mathrm{Id}_E$ for all $z\in D$, and let $h:D\to E$ be $C^\infty$. Suppose that for some $\rho>0$ and $M\in\mathbb{R}$,
--   $$\big\|\partial_s h(z)+\bar J(z)\,\partial_t h(z)\big\|\le M\,\|h(z)\|\qquad(|z|<\rho),$$
--   where $z=s+it$. Then there are $\varepsilon>0$, a constant $C$, and a holomorphic map $f:D_\varepsilon\to\mathbb{C}^n$ such that
--   $$\|f(z)\|\le C\,\|h(z)\|\quad\text{and}\quad\|h(z)\|\le C\,\|f(z)\|\qquad(|z|<\varepsilon).$$
--
--   So a solution of a linear Cauchy–Riemann type differential inequality is, near $0$, comparable in size to a holomorphic map. In particular its zeros near $0$ and their orders of vanishing are those of a holomorphic map.
--
--   **Formalization Note** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)` and $\dim_{\mathbb{R}}E=2n$ is `Module.finrank ℝ E = 2 * n`. $\bar J$ and $h$ are `ContDiffOn ℝ ∞` on `ball 0 1`, and $\partial_s h(z)$, $\partial_t h(z)$ are `fderiv ℝ h z 1`, `fderiv ℝ h z Complex.I`. The inequality is assumed on `ball 0 ρ` only. Holomorphy of $f$ is `DifferentiableOn ℂ f (ball 0 ε)`. No upper bound on $\varepsilon$ and no sign of $C$ is asserted.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.26 and Proposition 2.28

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic

namespace JHolomorphic

open Metric Filter Topology
open scoped ContDiff

/-- A smooth `h` with `‖∂ₛh + J̄(z) ∂ₜh‖ ≤ M ‖h‖` near `0` is, near `0`, comparable in norm to a
holomorphic `ℂⁿ`-valued map. -/
theorem exists_holomorphic_norm_comparable_of_norm_dbar_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ)
    (hn : Module.finrank ℝ E = 2 * n) (Jbar : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E)
    (h : ℂ → E) (hh : ContDiffOn ℝ ∞ h (ball 0 1)) (ρ M : ℝ) (hρ : 0 < ρ)
    (hM : ∀ z ∈ ball (0 : ℂ) ρ,
      ‖fderiv ℝ h z 1 + Jbar z (fderiv ℝ h z Complex.I)‖ ≤ M * ‖h z‖) :
    ∃ ε > (0 : ℝ), ∃ C : ℝ, ∃ f : ℂ → EuclideanSpace ℂ (Fin n),
      DifferentiableOn ℂ f (ball 0 ε) ∧
        ∀ z ∈ ball (0 : ℂ) ε, ‖f z‖ ≤ C * ‖h z‖ ∧ ‖h z‖ ≤ C * ‖f z‖ := by
  sorry

end JHolomorphic
