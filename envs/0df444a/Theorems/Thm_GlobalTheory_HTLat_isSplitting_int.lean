-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_isSplitting_int
-- name    : GlobalTheory.HTLat.isSplitting_int
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:41.570688+00:00
-- url     : https://prove2.me/theorems/b6d1e2d4-f84a-4bf2-8f0f-03b1dde5aa7f
-- title:
--   HTLat: is Splitting int
-- statement:
--   The HTLat construction uses the is Splitting int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L124-L127

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

theorem GlobalTheory.HTLat.isSplitting_int (R : Type) [CommRing R] :
    IsSplitting (fun _ : Unit => Int.castRingHom R) := by sorry
