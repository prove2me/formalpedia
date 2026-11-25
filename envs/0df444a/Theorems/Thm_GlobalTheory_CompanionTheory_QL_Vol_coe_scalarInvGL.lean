-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Vol_coe_scalarInvGL
-- name    : GlobalTheory.CompanionTheory.QL.Vol.coe_scalarInvGL
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:19:01.004751+00:00
-- url     : https://prove2.me/theorems/f3384ec5-5720-48a2-b397-063d9601d7de
-- title:
--   Vol: coe scalar Inv GL
-- statement:
--   The Vol construction uses the coe scalar Inv GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureUniformizerMultipleMatrices.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureUniformizerMultipleMatrices.lean#L14-L16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslateStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Vol

theorem GlobalTheory.CompanionTheory.QL.Vol.coe_scalarInvGL {F : Type} [Field F] (m : ℕ) (x : F) (hx : x ≠ 0) :
    ((scalarInvGL m x hx : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal (fun _ => x⁻¹) := by sorry
