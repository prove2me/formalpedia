-- Prove2me | Theorems.Thm_GlobalTheory_TorsionMatrix_val_mul_smul
-- name    : GlobalTheory.TorsionMatrix.val_mul_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:07:54.914828+00:00
-- url     : https://prove2.me/theorems/dfd0984f-3efa-493b-b971-26eb72f1b4b6
-- title:
--   Torsion Matrix: val mul smul
-- statement:
--   The Torsion Matrix construction uses the val mul smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L199-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean#L199-L201

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
variable {Q κ : Type} [AddCommGroup Q] [Fintype κ] {N : ℕ} [NeZero N]

theorem GlobalTheory.TorsionMatrix.val_mul_smul {x : Q} (hx : N • x = 0) (a b : ZMod N) :
    (a * b).val • x = b.val • a.val • x := by sorry
