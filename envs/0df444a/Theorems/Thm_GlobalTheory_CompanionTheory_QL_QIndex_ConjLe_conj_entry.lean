-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_ConjLe_conj_entry
-- name    : GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.conj_entry
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:48.71066+00:00
-- url     : https://prove2.me/theorems/bdf06130-010b-4c5f-99f5-4c109026faea
-- title:
--   Conj Le: conj entry
-- statement:
--   The Conj Le construction uses the conj entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DiagonalConjugateCongruenceBox.lean#L79-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DiagonalConjugateCongruenceBox.lean#L79-L90

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DiagonalConjugateCongruenceBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
variable {F : Type} [Field F]

theorem GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.conj_entry {n : ℕ} (g p : GL (Fin n) F) {dd : Fin n → F}
    (hD : (g : Matrix (Fin n) (Fin n) F) = diagonal dd) (a b : Fin n) :
    (((g * p * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1) a b =
      dd a * ((p : Matrix (Fin n) (Fin n) F) - 1) a b * (dd b)⁻¹ := by sorry
