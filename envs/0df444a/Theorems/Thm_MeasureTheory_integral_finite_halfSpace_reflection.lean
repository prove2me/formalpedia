-- Prove2me | Theorems.Thm_MeasureTheory_integral_finite_halfSpace_reflection
-- name    : MeasureTheory.integral_finite_halfSpace_reflection
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T13:27:30.596964+00:00
-- url     : https://prove2.me/theorems/f56fa257-62b8-4375-9261-95de14fd626c
-- title:
--   Integral adjoint of a finite family of normal reflection dilations
-- statement:
--   Let f be locally integrable with respect to volume restricted to the positive coordinate half-space H, let b_j be finitely many positive real dilation factors, and let c_j be arbitrary real coefficients. Retain f on H and extend it below the boundary by the sum of c_j f(x with normal coordinate replaced by -b_j x_i). Its integral against any continuous compactly supported test equals the integral on H of f against the adjoint test: the original test plus the sum of (c_j/b_j) times the test evaluated with normal coordinate -x_i/b_j. The separating hyperplane has zero volume, and the inverse absolute determinant is 1/b_j. No weak derivatives or moment conditions are involved. The empty family is allowed. This is an independent finite-family change-of-variables interface, extending the signed isometric coordinate fold to arbitrary positive dilations.
-- source:
--   Sung-Jin Oh, Lecture Notes for Math 222A (March 19, 2024), Proposition 11.13, proof Step 2, printed p. 158, equations (11.3)-(11.4), https://math.berkeley.edu/~sjoh/pdfs/notes-math222a.pdf . Independent analytic and calculus interfaces for the distributional justification; the weak-data boundary step is an additional cutoff argument, not attributed to the smooth calculation alone.

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
open MeasureTheory
set_option autoImplicit false

theorem MeasureTheory.integral_finite_halfSpace_reflection
    {n N : ℕ} (i : Fin n) (b c : Fin N → ℝ) (hb : ∀ j, 0 < b j)
    (f φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : LocallyIntegrable f (volume.restrict {x | 0 < x i}))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    (∫ x, (if 0 < x i then f x else
      ∑ j : Fin N, c j * f (WithLp.toLp 2
        (Function.update (fun k => x k) i (-b j * x i)))) * φ x) =
    ∫ x in {x : EuclideanSpace ℝ (Fin n) | 0 < x i},
      f x * (φ x + ∑ j : Fin N, (c j / b j) *
        φ (WithLp.toLp 2 (Function.update (fun k => x k) i (-(b j)⁻¹ * x i)))) := by sorry
