-- Prove2me | Theorems.Thm_GlobalTheory_TorsionMatrix_norm_card_quot_span
-- name    : GlobalTheory.TorsionMatrix.norm_card_quot_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:07:27.149487+00:00
-- url     : https://prove2.me/theorems/6f35bd12-ea75-4fea-b5ef-b036b142edf3
-- title:
--   Torsion Matrix: norm card quot span
-- statement:
--   The Torsion Matrix construction uses the norm card quot span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L15-L26

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

theorem GlobalTheory.TorsionMatrix.norm_card_quot_span (l : ℕ) [Fact l.Prime] {a : ℤ_[l]} (ha : a ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span {a}) : ℕ) : ℚ_[l])‖ = ‖a‖ := by sorry
