-- Prove2me | Theorems.Thm_MeasureTheory_MemLp_comp_abs_coordinate
-- name    : MeasureTheory.MemLp.comp_abs_coordinate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T17:45:51.217746+00:00
-- url     : https://prove2.me/theorems/ae4e8967-f440-4618-a0d5-46fb60eb3db3
-- title:
--   Lp membership is preserved by folding a coordinate into a half-space
-- statement:
--   Fix a coordinate $i$ in $\mathbb R^n$ and let $H_i=\{x:x_i>0\}$. Let $R_i$ replace $x_i$ by $|x_i|$ and fix all other coordinates. For every exponent $0\le p\le\infty$,
--   $$f\in L^p(H_i)\quad\Longrightarrow\quad f\circ R_i\in L^p(\mathbb R^n).$$
--   The endpoint $p=0$ means almost-everywhere strong measurability under the Mathlib convention. Values on the boundary hyperplane are arbitrary. Zero-extend $f$ from $H_i$, reflect that extension, and add; the result agrees with $f\circ R_i$ off the null hyperplane.
-- source:
--   Auxiliary measure-theoretic lemma for the reflection construction in Hunter, Notes on Partial Differential Equations, revised 2014-06-18, section 3.9, printed pp. 71–72. https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf . The proof uses invariance of Lebesgue measure under a coordinate reflection and the nullity of a proper vector subspace.

import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem MeasureTheory.MemLp.comp_abs_coordinate (n : ℕ) (p : ℝ≥0∞) (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f p (volume.restrict {x | 0 < x i})) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) =>
      f (WithLp.toLp 2 (fun j => if j = i then |x j| else x j))) p volume := by sorry
