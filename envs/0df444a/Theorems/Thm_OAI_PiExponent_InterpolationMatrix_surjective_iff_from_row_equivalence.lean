-- Prove2me | Theorems.Thm_OAI_PiExponent_InterpolationMatrix_surjective_iff_from_row_equivalence
-- name    : OAI.PiExponent.InterpolationMatrix.surjective_iff_from_row_equivalence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T05:08:28.065792+00:00
-- url     : https://prove2.me/theorems/2d3c2d83-a442-41bd-b81b-b78eaba428a1
-- title:
--   Invertible row transformations preserve surjectivity
-- statement:
--   Show that an invertible output-side matrix preserves surjectivity when multiplying another finite matrix. This removes the linear-algebra step from the parent. Prove it by identifying multiplication with composition of the represented linear maps and using bijectivity of `U.mulVecLin`; the argument also covers empty finite index types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Complex.Basic
open scoped BigOperators

theorem OAI.PiExponent.InterpolationMatrix.surjective_iff_from_row_equivalence
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι ι ℂ) (M M' : Matrix ι κ ℂ)
    (hU : Function.Bijective U.mulVecLin) (hfactor : M = U * M') :
    Function.Surjective M.mulVecLin ↔ Function.Surjective M'.mulVecLin := by sorry
