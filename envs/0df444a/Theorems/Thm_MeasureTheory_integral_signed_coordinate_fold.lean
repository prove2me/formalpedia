-- Prove2me | Theorems.Thm_MeasureTheory_integral_signed_coordinate_fold
-- name    : MeasureTheory.integral_signed_coordinate_fold
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T18:19:16.448245+00:00
-- url     : https://prove2.me/theorems/514c60b3-9274-4fcd-9e1c-6b5ddd6ee174
-- title:
--   Signed coordinate folding under a compactly supported test
-- statement:
--   Let $H=\{x\in\mathbb R^n:x_i>0\}$, let $R_i$ reverse coordinate $i$, and put $F_i(x)_i=|x_i|$, with all other coordinates unchanged. Suppose $f$ is locally integrable with respect to Lebesgue measure restricted to $H$, and $\varphi$ is continuous with compact support. For any real constant $c$,
--   $$\int_{\mathbb R^n} (\mathbf 1_{x_i\ge0}+c\mathbf 1_{x_i<0}) f(F_i x)\varphi(x)\,dx
--   =\int_H f(x)\bigl(\varphi(x)+c\varphi(R_i x)\bigr)\,dx.$$
--   The hypothesis includes integrability near the boundary, since local integrability is for the restricted measure on the whole ambient space. The choices $c=1$ and $c=-1$ give the even and odd reflection formulas. Values on the coordinate hyperplane do not affect either integral.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised June 18, 2014, section 3.9, printed pp. 71–72, reflection construction preceding Theorem 3.41, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf . This auxiliary lemma is derived for the distributional justification of the construction; it is not a separately numbered source theorem.

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
set_option autoImplicit false

theorem MeasureTheory.integral_signed_coordinate_fold (n : ℕ) (i : Fin n) (c : ℝ)
    (f φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : LocallyIntegrable f (volume.restrict {x | 0 < x i}))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    (∫ x : EuclideanSpace ℝ (Fin n),
      (if x i < 0 then c * f (WithLp.toLp 2 (fun j => if j = i then |x j| else x j))
       else f (WithLp.toLp 2 (fun j => if j = i then |x j| else x j))) * φ x) =
    ∫ x in {x : EuclideanSpace ℝ (Fin n) | 0 < x i},
      f x * (φ x + c * φ (WithLp.toLp 2 (fun j => if j = i then -x j else x j))) := by sorry
