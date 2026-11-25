-- Prove2me | Theorems.Thm_GlobalTheory_TorsionMatrix_exists_zmod_basis
-- name    : GlobalTheory.TorsionMatrix.exists_zmod_basis
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:10:44.11384+00:00
-- url     : https://prove2.me/theorems/9720651f-aa32-5d8c-bb07-647a686851e4
-- title:
--   Torsion Matrix: exists zmod basis
-- statement:
--   The Torsion Matrix construction uses the exists zmod basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L68-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L68-L85

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

theorem GlobalTheory.TorsionMatrix.exists_zmod_basis (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod l) V] (hc1 : Nat.card V = l ^ m) :
    ∃ b : Fin m → V, ∀ x : V, ∃! t : Fin m → ZMod l, x = ∑ j, (t j).val • b j := by sorry
