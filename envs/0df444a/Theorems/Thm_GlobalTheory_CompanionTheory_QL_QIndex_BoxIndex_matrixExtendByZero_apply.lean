-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_matrixExtendByZero_apply
-- name    : GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.matrixExtendByZero_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:57.235723+00:00
-- url     : https://prove2.me/theorems/05a5bde8-f1cb-4099-8d2c-6ac7441abb29
-- title:
--   Box Index: matrix Extend By Zero apply
-- statement:
--   The Box Index construction uses the matrix Extend By Zero apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RelIndexBoxLatticesProduct.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RelIndexBoxLatticesProduct.lean#L115-L118

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
open GlobalTheory.CompanionTheory.QL.NormalisedValue GlobalTheory.CompanionTheory.SplitRow.IdxV
variable {F : Type} [Field F]

theorem GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.matrixExtendByZero_apply {n : ℕ} (β : Fin n → ℕ) (x : Idx β → F) (p : Idx β) :
    ext0 β x p.1.1 p.1.2 = x p := by sorry
