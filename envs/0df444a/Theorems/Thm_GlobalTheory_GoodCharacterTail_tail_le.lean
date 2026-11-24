-- Prove2me | Theorems.Thm_GlobalTheory_GoodCharacterTail_tail_le
-- name    : GlobalTheory.GoodCharacterTail.tail_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:05:42.03597+00:00
-- url     : https://prove2.me/theorems/e3720c95-9b12-421a-9306-e05866a0a47b
-- title:
--   Good Character Tail: tail le
-- statement:
--   The Good Character Tail construction uses the tail le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TailAndSumBound.lean#L13-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TailAndSumBound.lean#L13-L46

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2IntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TailAndSumBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open GlobalTheory GlobalTheory.GoodCharacterTail
open Formalism.HermitianLattices.GL2PrimeSums

theorem GlobalTheory.GoodCharacterTail.tail_le (a : ℕ → ℂ) (S : ℂ)
    (hS : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S))
    (Z B : ℝ) (hZ : 1 ≤ Z)
    (hB : ∀ U : ℝ, Z ≤ U → ‖psum a Z‖ / Z + (∫ u in Z..U, ‖psum a u‖ / u ^ 2) ≤ B) :
    ‖S - ∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ)‖ ≤ B := by sorry
