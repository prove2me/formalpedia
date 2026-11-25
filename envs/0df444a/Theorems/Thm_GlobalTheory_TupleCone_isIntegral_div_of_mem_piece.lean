-- Prove2me | Theorems.Thm_GlobalTheory_TupleCone_isIntegral_div_of_mem_piece
-- name    : GlobalTheory.TupleCone.isIntegral_div_of_mem_piece
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:08:12.072311+00:00
-- url     : https://prove2.me/theorems/62f1c605-7d1e-4439-bf69-eae2561dcafc
-- title:
--   Tuple Cone: is Integral div of mem piece
-- statement:
--   The Tuple Cone construction uses the is Integral div of mem piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L215-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L215-L229

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

theorem GlobalTheory.TupleCone.isIntegral_div_of_mem_piece (i : σ) {n : ℕ} {a : L} (ha : a ∈ piece o t n) :
    IsIntegral (ratioRing o t i) (a / t i ^ n) := by sorry
