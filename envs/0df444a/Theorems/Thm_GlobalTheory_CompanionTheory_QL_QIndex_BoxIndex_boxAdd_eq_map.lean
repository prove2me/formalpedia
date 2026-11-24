-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_boxAdd_eq_map
-- name    : GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.boxAdd_eq_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:57:19.00369+00:00
-- url     : https://prove2.me/theorems/d6f16b16-527e-4f2a-bc2e-6c0e5fbee682
-- title:
--   Box Index: box Add eq map
-- statement:
--   The Box Index construction uses the box Add eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RelIndexBoxLatticesProduct.lean#L125-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RelIndexBoxLatticesProduct.lean#L125-L147

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

theorem GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.boxAdd_eq_map (O : Subring F) {n : ℕ} (β : Fin n → ℕ) (c : Fin n → Fin n → F) :
    boxAdd O β c =
      (AddSubgroup.pi Set.univ fun p : Idx β => line O (c p.1.1 p.1.2)).map (ext0 β) := by sorry
