-- Prove2me | Theorems.Thm_HunterPDE_Shared_iteratedPartial_sum_coordinate_pullback
-- name    : HunterPDE.Shared.iteratedPartial_sum_coordinate_pullback
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T13:24:07.085158+00:00
-- url     : https://prove2.me/theorems/20bb3313-69e4-429f-a763-15aef3053e2e
-- title:
--   Iterated coordinate derivatives of finite sums of diagonal pullbacks
-- statement:
--   Let each linear map fix all coordinate basis vectors except a common distinguished direction, which it multiplies by an arbitrary real scalar. For a finite family of smooth real functions and constant coefficients, an ordered word of coordinate derivatives of their weighted pullbacks equals the weighted sum of the pulled-back derivatives, with each term multiplied by its distinguished scalar to the number of occurrences of that direction in the word. The scalars may be zero, the maps need not be invertible, and the derivative word and finite family may be empty.
-- source:
--   Sung-Jin Oh, Lecture Notes for Math 222A (March 19, 2024), Proposition 11.13, proof Step 2, printed p. 158, equations (11.3)-(11.4), https://math.berkeley.edu/~sjoh/pdfs/notes-math222a.pdf . Independent analytic and calculus interfaces for the distributional justification; the weak-data boundary step is an additional cutoff argument, not attributed to the smooth calculation alone.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
open HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem HunterPDE.Shared.iteratedPartial_sum_coordinate_pullback
    {n : ℕ} {ι : Type*} [Fintype ι] (i : Fin n) (a t : ι → ℝ)
    (e : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : ∀ j k, e j (EuclideanSpace.single k 1) =
      (if k = i then t j else 1) • EuclideanSpace.single k 1)
    (u : ι → EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ∀ j, ContDiff ℝ ∞ (u j)) (l : List (Fin n)) :
    iteratedPartial (fun x => ∑ j, a j * u j (e j x)) l =
      fun x => ∑ j, (a j * t j ^ l.count i) * iteratedPartial (u j) l (e j x) := by sorry
