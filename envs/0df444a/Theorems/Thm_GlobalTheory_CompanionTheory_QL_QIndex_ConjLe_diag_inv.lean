-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_ConjLe_diag_inv
-- name    : GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.diag_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:00.921588+00:00
-- url     : https://prove2.me/theorems/9ec97377-f9df-49c4-9713-31b134d50789
-- title:
--   Conj Le: diag inv
-- statement:
--   The Conj Le construction uses the diag inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DiagonalConjugateCongruenceBox.lean#L58-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DiagonalConjugateCongruenceBox.lean#L58-L77

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

theorem GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.diag_inv {n : ℕ} (g : GL (Fin n) F) {dd : Fin n → F}
    (hD : (g : Matrix (Fin n) (Fin n) F) = diagonal dd) :
    (∀ a, dd a ≠ 0) ∧
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal fun a => (dd a)⁻¹ := by sorry
