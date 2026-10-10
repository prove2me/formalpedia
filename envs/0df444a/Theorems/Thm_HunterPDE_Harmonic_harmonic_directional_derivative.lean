-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_harmonic_directional_derivative
-- name    : HunterPDE.Harmonic.harmonic_directional_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T15:25:23.601774+00:00
-- url     : https://prove2.me/theorems/e134412e-65d2-470c-ad0f-498b063cd067
-- title:
--   Constant-direction derivatives preserve harmonicity on open sets
-- statement:
--   Let $n\ge1$, let $\Omega\subseteq\mathbb R^n$ be open, and let $u:\mathbb R^n\to\mathbb R$ be harmonic near every point of $\Omega$. For every constant vector $v\in\mathbb R^n$, the directional derivative is harmonic on the same open set:
--
--   $$D_vu(y)=Du(y)[v],\qquad \Delta(D_vu)=0\quad\text{on }\Omega.$$
--
--   This closure property allows interior estimates to be applied repeatedly to derivatives of harmonic functions.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, pp. 21 and 23–24, Theorems 2.1–2.2 and proof of Theorem 2.9; generalized to constant directions / families satisfying first-derivative estimates.

import Theorems.Thm_HunterPDE_Harmonic_mean_value_property
import Theorems.Thm_HunterPDE_Harmonic_smooth_of_mean_value_property
import Theorems.Thm_HunterPDE_Harmonic_directional_derivative_mean_value
import Mathlib.Analysis.Calculus.ContDiff.Comp

open HunterPDE.Harmonic Filter Topology Laplacian
open scoped ContDiff
set_option autoImplicit false

theorem HunterPDE.Harmonic.harmonic_directional_derivative {n : ℕ} (hn : 0 < n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hΩ : IsOpen Ω) (hu : InnerProductSpace.HarmonicOnNhd u Ω)
    (v : EuclideanSpace ℝ (Fin n)) :
    InnerProductSpace.HarmonicOnNhd (fun y => fderiv ℝ u y v) Ω := by sorry
