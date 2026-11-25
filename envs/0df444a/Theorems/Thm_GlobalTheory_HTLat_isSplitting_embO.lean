-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_isSplitting_embO
-- name    : GlobalTheory.HTLat.isSplitting_embO
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:33.511718+00:00
-- url     : https://prove2.me/theorems/08ed4a90-3a84-45b4-aac8-e3055830d42c
-- title:
--   HTLat: is Splitting emb O
-- statement:
--   The HTLat construction uses the is Splitting emb O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L108-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L108-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
set_option autoImplicit false
open scoped TensorProduct NNReal NumberField Pointwise
variable {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.HTLat.isSplitting_embO [IsAlgClosed C] [CharZero C] :
    _root_.GlobalTheory.EigenSplit.IsSplitting
      (fun φ : E →+* C => (algebraMap O C).comp (_root_.GlobalTheory.HTLat.embO hv φ)) := by sorry
