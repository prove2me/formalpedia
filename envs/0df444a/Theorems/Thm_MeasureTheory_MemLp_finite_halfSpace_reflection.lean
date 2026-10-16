-- Prove2me | Theorems.Thm_MeasureTheory_MemLp_finite_halfSpace_reflection
-- name    : MeasureTheory.MemLp.finite_halfSpace_reflection
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T09:36:08.711589+00:00
-- url     : https://prove2.me/theorems/5023d8f2-b036-404e-9c5e-47417e0ece51
-- title:
--   Finite sums of normally dilated reflections preserve half-space Lp data
-- statement:
--   Let H be the open half-space x_i>0 in Euclidean n-space. Let b_j>0 and c_j be arbitrary finite families of real numbers. For any extended nonnegative exponent p, a real function f in Lp(H) gives an Lp function on the whole space by retaining f on H and setting its value on the complement to the sum of c_j f(T_j x), where T_j multiplies coordinate i by -b_j and fixes the others. The assertion includes p=0 and p=infinity, and the empty family. Values on the separating hyperplane are irrelevant. This statement requires no moment matching and no derivatives.
-- source:
--   Sung-Jin Oh, Lecture Notes for Math 222A, March 19, 2024, Proposition 11.13, proof Step 2, printed p. 158, equations (11.3)-(11.4), https://math.berkeley.edu/~sjoh/pdfs/notes-math222a.pdf . Lp change-of-variables component of the reflected extension, generalized to any exponent, any coordinate and arbitrary positive normal dilations; no moment identities are needed for integrability.

import Theorems.Thm_MeasureTheory_MemLp_comp_continuousLinearEquiv_volume
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem MeasureTheory.MemLp.finite_halfSpace_reflection {n N : ℕ} (i : Fin n) (p : ℝ≥0∞)
    (b c : Fin N → ℝ) (hb : ∀ j, 0 < b j)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f p (volume.restrict {x | 0 < x i})) :
    MemLp (fun x => if 0 < x i then f x else
      ∑ j : Fin N, c j * f (WithLp.toLp 2
        (Function.update (fun l => x l) i (-b j * x i)))) p volume := by sorry
