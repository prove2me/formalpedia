-- Prove2me | Theorems.Thm_GlobalTheory_TailIntegralOfSummatory_integral_eq
-- name    : GlobalTheory.TailIntegralOfSummatory.integral_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:51:03.554861+00:00
-- url     : https://prove2.me/theorems/ef8c7f60-f819-479c-a2e1-312d7dbc5e2e
-- title:
--   Tail Integral Of Summatory: integral eq
-- statement:
--   The Tail Integral Of Summatory construction uses the integral eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/KroneckerReal.lean#L61-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/KroneckerReal.lean#L61-L107

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open Formalism.HermitianLattices.GL2PrimeSums
open GlobalTheory GlobalTheory.TailIntegralOfSummatory

theorem GlobalTheory.TailIntegralOfSummatory.integral_eq (a : ℕ → ℂ) {y U : ℝ} (hy : 1 ≤ y) (hU : y ≤ U) :
    ∫ u in y..U, psum a u / (u : ℂ) ^ 2 =
      (recSum a ⌊U⌋₊ - psum a U / U) - (recSum a ⌊y⌋₊ - psum a y / y) := by sorry
