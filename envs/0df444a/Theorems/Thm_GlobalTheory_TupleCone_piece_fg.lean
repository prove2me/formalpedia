-- Prove2me | Theorems.Thm_GlobalTheory_TupleCone_piece_fg
-- name    : GlobalTheory.TupleCone.piece_fg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:26.106181+00:00
-- url     : https://prove2.me/theorems/dc6aefad-83c6-5b08-bf30-832088058416
-- title:
--   Tuple Cone: piece fg
-- statement:
--   The Tuple Cone construction uses the piece fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L314-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L314-L317

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

theorem GlobalTheory.TupleCone.piece_fg (n : ℕ) : (piece o t n).FG := by sorry
