-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_card_embeddings_of_splits
-- name    : GlobalTheory.EigenSplit.card_embeddings_of_splits
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:16.678869+00:00
-- url     : https://prove2.me/theorems/ad0d70bf-0806-4ccf-a57d-bbb71d30c20c
-- title:
--   Eigen Split: card embeddings of splits
-- statement:
--   The Eigen Split construction uses the card embeddings of splits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L759-L763
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L759-L763

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.EigenSplit.card_embeddings_of_splits {L : Type*} [Field L] [CharZero L] [Fintype (E →+* L)]
    (hL : ∀ x : E, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits) :
    Fintype.card (E →+* L) = Module.finrank ℚ E := by sorry
