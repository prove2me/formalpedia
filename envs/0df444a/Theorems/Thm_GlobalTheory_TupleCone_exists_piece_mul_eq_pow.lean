-- Prove2me | Theorems.Thm_GlobalTheory_TupleCone_exists_piece_mul_eq_pow
-- name    : GlobalTheory.TupleCone.exists_piece_mul_eq_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:09:06.32715+00:00
-- url     : https://prove2.me/theorems/783a799d-5555-4430-acbb-968a8a48f74e
-- title:
--   Tuple Cone: exists piece mul eq pow
-- statement:
--   The Tuple Cone construction uses the exists piece mul eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L352-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L352-L368

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
variable (o t) [IsDedekindDomain o] [CharZero L] [Algebra.EssFiniteType o L] [Finite σ]

theorem GlobalTheory.TupleCone.exists_piece_mul_eq_pow : ∃ e : ℕ, 0 < e ∧ ∀ j, 0 < j →
    piece o t (j * e) = piece o t e ^ j := by sorry
