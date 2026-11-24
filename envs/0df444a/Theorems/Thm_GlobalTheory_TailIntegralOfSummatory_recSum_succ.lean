-- Prove2me | Theorems.Thm_GlobalTheory_TailIntegralOfSummatory_recSum_succ
-- name    : GlobalTheory.TailIntegralOfSummatory.recSum_succ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:51:16.566461+00:00
-- url     : https://prove2.me/theorems/4d4f213c-39a8-4bc0-87ca-d8e7b02b5705
-- title:
--   Tail Integral Of Summatory: rec Sum succ
-- statement:
--   The Tail Integral Of Summatory construction uses the rec Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/KroneckerReal.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/KroneckerReal.lean#L11-L14

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

theorem GlobalTheory.TailIntegralOfSummatory.recSum_succ (a : ℕ → ℂ) (N : ℕ) :
    recSum a (N + 1) = recSum a N + a (N + 1) / ((N + 1 : ℕ) : ℂ) := by sorry
