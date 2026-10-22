-- Prove2me | Theorems.Thm_NewtonCartan_contDiff_primitive_of_closed_oneForm
-- name    : NewtonCartan.contDiff_primitive_of_closed_oneForm
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:51:01.768994+00:00
-- url     : https://prove2.me/theorems/f5c16b4b-b381-4e08-b6cc-4e69952926b4
-- title:
--   ContDiff primitive of a closed ContDiff 1-form
-- statement:
--   Let $X$ be a finite-dimensional real normed space and let $\omega : X \to \mathrm{L}(X,\mathbb{R})$ be a $C^\infty$ closed $1$-form, meaning
--   $$
--   D\omega_a(x,y)=D\omega_a(y,x)\qquad\text{for all }a,x,y\in X.
--   $$
--   Then there exists a $C^\infty$ potential $\varphi : X \to \mathbb{R}$ such that $D\varphi_a=\omega_a$ at every point.
--
--   The result upgrades Mathlib's Poincaré lemma on the convex open set $\mathbb{R}^n\cong X$ by combining the existence of a Fréchet primitive with `contDiff_infty_iff_fderiv`: since the derivative equals the already smooth form $\omega$, the primitive is $C^\infty$. This is the analytic engine for integrating Trautman spatial Hessians on each constant-$t$ slice in Malament/Weatherall Proposition 2.2.
--
--   Formalization Note. Infrastructure lemma for `NewtonCartan.exists_potential_of_spatial_F`.

import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped ContDiff Topology
open MeasureTheory Set Convex

namespace NewtonCartan

theorem contDiff_primitive_of_closed_oneForm
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [FiniteDimensional ℝ X]
    (omegaForm : X → X →L[ℝ] ℝ) (hω : ContDiff ℝ ∞ omegaForm)
    (hclosed : ∀ a x y, fderiv ℝ omegaForm a x y = fderiv ℝ omegaForm a y x) :
    ∃ φ : X → ℝ, ContDiff ℝ ∞ φ ∧ ∀ a, HasFDerivAt φ (omegaForm a) a := by sorry

end NewtonCartan
