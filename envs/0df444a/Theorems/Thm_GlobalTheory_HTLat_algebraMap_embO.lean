-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_algebraMap_embO
-- name    : GlobalTheory.HTLat.algebraMap_embO
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:01:28.267972+00:00
-- url     : https://prove2.me/theorems/277e50d7-3e74-414f-85cf-715f29500acc
-- title:
--   HTLat: algebra Map emb O
-- statement:
--   The HTLat construction uses the algebra Map emb O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L92-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L92-L101

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
omit [NumberField E]

theorem GlobalTheory.HTLat.algebraMap_embO (φ : E →+* C) (a : 𝓞 E) :
    algebraMap O C (_root_.GlobalTheory.HTLat.embO hv φ a) = φ a := by sorry
