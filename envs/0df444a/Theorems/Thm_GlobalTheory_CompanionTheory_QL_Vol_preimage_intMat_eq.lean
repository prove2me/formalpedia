-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Vol_preimage_intMat_eq
-- name    : GlobalTheory.CompanionTheory.QL.Vol.preimage_intMat_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:14:26.183652+00:00
-- url     : https://prove2.me/theorems/50e484df-87d8-5941-8d6b-86399404dcae
-- title:
--   Vol: preimage int Mat eq
-- statement:
--   The Vol construction uses the preimage int Mat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureUniformizerMultipleMatrices.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureUniformizerMultipleMatrices.lean#L18-L29

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

theorem GlobalTheory.CompanionTheory.QL.Vol.preimage_intMat_eq {F : Type} [Field F] (O : Subring F) {ϖ : F} (hϖ : ϖ ≠ 0) (n m : ℕ) :
    (fun x : Matrix (Fin n) (Fin m) F => x * ((scalarInvGL m ϖ hϖ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) ⁻¹'
      intMat O n m = (IIset O ϖ : Set (Matrix (Fin n) (Fin m) F)) := by sorry
