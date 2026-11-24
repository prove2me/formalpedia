-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_extendByZero_injective
-- name    : GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.extendByZero_injective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:49.110874+00:00
-- url     : https://prove2.me/theorems/f041c51e-1d6c-4ade-9a5e-b7521de19a7b
-- title:
--   Box Index: extend By Zero injective
-- statement:
--   The Box Index construction uses the extend By Zero injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RelIndexBoxLatticesProduct.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RelIndexBoxLatticesProduct.lean#L120-L123

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

theorem GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.extendByZero_injective {n : ℕ} (β : Fin n → ℕ) : Function.Injective (ext0 (F := F) β) := by sorry
