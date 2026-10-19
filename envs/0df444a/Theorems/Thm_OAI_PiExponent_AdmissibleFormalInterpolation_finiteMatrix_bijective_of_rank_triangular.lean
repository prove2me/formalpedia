-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finiteMatrix_bijective_of_rank_triangular
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.finiteMatrix_bijective_of_rank_triangular
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:08:16.887294+00:00
-- url     : https://prove2.me/theorems/6dbc35ed-dde1-4400-8a40-1d8e6dab93b5
-- title:
--   Bijectivity of a strictly triangular finite matrix
-- statement:
--   A finite complex matrix whose diagonal entries are one and whose nonzero off-diagonal entries strictly increase a natural-number rank from row to column defines a bijective linear map.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.finiteMatrix_bijective_of_rank_triangular
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (rank : ι → ℕ) (M : Matrix ι ι ℂ)
    (hdiag : ∀ i, M i i = 1)
    (htri : ∀ i j, i ≠ j → M i j ≠ 0 → rank i < rank j) :
    Function.Bijective M.mulVecLin := by sorry
