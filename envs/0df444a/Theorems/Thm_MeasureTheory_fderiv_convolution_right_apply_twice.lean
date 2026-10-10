-- Prove2me | Theorems.Thm_MeasureTheory_fderiv_convolution_right_apply_twice
-- name    : MeasureTheory.fderiv_convolution_right_apply_twice
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T10:08:36.948913+00:00
-- url     : https://prove2.me/theorems/97e699c0-a223-4937-8b28-357b819d0d48
-- title:
--   Two directional derivatives pass to a compactly supported convolution source
-- statement:
--   Let K be a locally integrable real kernel on Euclidean n-space, and let f be a twice continuously differentiable real function with compact support. For any point x and any fixed vectors v,w, differentiation of the convolution twice passes to the source:
--
--   $$D_vD_w(K*f)(x)=(K*(D_vD_w f))(x).$$
--
--   The kernel need not be differentiable or integrable over the entire space. This generalizes the source-differentiation step in Hunter Eq. (2.26) from the Newtonian kernel and coordinate directions to any locally integrable kernel and arbitrary directions. Mathlib supplies the first Fréchet derivative of convolution; applying it twice gives this statement.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed pp. 37–38, Theorem 2.26, Eqs. (2.26)–(2.28).

import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff

theorem MeasureTheory.fderiv_convolution_right_apply_twice (n : ℕ) (K f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : LocallyIntegrable K volume) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z => fderiv ℝ (K ⋆[lsmul ℝ ℝ] f) z w) x v =
      (K ⋆[lsmul ℝ ℝ] (fun y => fderiv ℝ (fun z => fderiv ℝ f z w) y v)) x := by sorry
