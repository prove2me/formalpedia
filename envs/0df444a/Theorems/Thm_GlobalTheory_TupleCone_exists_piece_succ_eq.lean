-- Prove2me | Theorems.Thm_GlobalTheory_TupleCone_exists_piece_succ_eq
-- name    : GlobalTheory.TupleCone.exists_piece_succ_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:03:16.707875+00:00
-- url     : https://prove2.me/theorems/f681e408-3423-4821-85b6-b3741fec2d47
-- title:
--   Tuple Cone: exists piece succ eq
-- statement:
--   The Tuple Cone construction uses the exists piece succ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L336-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIntegralRatioRingIffMemAdjoin.lean#L336-L350

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

theorem GlobalTheory.TupleCone.exists_piece_succ_eq : ∃ e : ℕ, 0 < e ∧ ∀ d, e ≤ d →
    piece o t (d + 1) = Submodule.span o (Set.range t) * piece o t d := by sorry
