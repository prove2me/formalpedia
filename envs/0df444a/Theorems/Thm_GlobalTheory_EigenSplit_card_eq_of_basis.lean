-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_card_eq_of_basis
-- name    : GlobalTheory.EigenSplit.card_eq_of_basis
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:37.3666+00:00
-- url     : https://prove2.me/theorems/2e10f636-820d-4dbf-8b19-fcbcbb5ada0b
-- title:
--   Eigen Split: card eq of basis
-- statement:
--   The Eigen Split construction uses the card eq of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L664-L666
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L664-L666

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
omit [DecidableEq ι]

theorem GlobalTheory.EigenSplit.card_eq_of_basis (b : Module.Basis ι ℤ (𝓞 E)) :
    Fintype.card ι = Module.finrank ℚ E := by sorry
