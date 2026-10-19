-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finiteMatrix_injective_of_rank_triangular
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.finiteMatrix_injective_of_rank_triangular
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:13:38.002958+00:00
-- url     : https://prove2.me/theorems/1a365b37-6d7c-4db2-b205-180999d14832
-- title:
--   Injectivity from strict rank triangularity
-- statement:
--   If a finite complex matrix has diagonal entries one and each nonzero off-diagonal entry goes from a lower row rank to a strictly higher column rank, its associated linear map is injective.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.finiteMatrix_injective_of_rank_triangular
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (rank : ι → ℕ) (M : Matrix ι ι ℂ)
    (hdiag : ∀ i, M i i = 1)
    (htri : ∀ i j, i ≠ j → M i j ≠ 0 → rank i < rank j) :
    Function.Injective M.mulVecLin := by sorry
