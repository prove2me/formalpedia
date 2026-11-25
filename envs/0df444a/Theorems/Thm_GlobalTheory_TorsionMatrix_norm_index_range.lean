-- Prove2me | Theorems.Thm_GlobalTheory_TorsionMatrix_norm_index_range
-- name    : GlobalTheory.TorsionMatrix.norm_index_range
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:15:15.499879+00:00
-- url     : https://prove2.me/theorems/99f77b0c-c288-4f57-b77c-72968b14a7aa
-- title:
--   Torsion Matrix: norm index range
-- statement:
--   The Torsion Matrix construction uses the norm index range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L28-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TorsionMatrix
open Matrix

theorem GlobalTheory.TorsionMatrix.norm_index_range (l : ℕ) [Fact l.Prime] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℤ_[l]) (hM : M.det ≠ 0) :
    ‖M.det‖ = ‖(((LinearMap.range M.mulVecLin).toAddSubgroup.index : ℕ) : ℚ_[l])‖ := by sorry
