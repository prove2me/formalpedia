-- Prove2me | Theorems.Thm_GlobalTheory_TupleCone_isIntegral_ratioRing_iff
-- name    : GlobalTheory.TupleCone.isIntegral_ratioRing_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:24.287631+00:00
-- url     : https://prove2.me/theorems/68e606ec-7a48-51da-b2c2-2fdcef0a97fe
-- title:
--   Tuple Cone: is Integral ratio Ring iff
-- statement:
--   The Tuple Cone construction uses the is Integral ratio Ring iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L231-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L231-L259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}

theorem GlobalTheory.TupleCone.isIntegral_ratioRing_iff {i : σ} (hi : t i ≠ 0) {f : L} :
    IsIntegral (ratioRing o t i) f ↔ ∃ n, f * t i ^ n ∈ piece o t n := by sorry
