-- Prove2me | Theorems.Thm_GlobalTheory_GaussTransport_iteratedDeriv_cexp_mul
-- name    : GlobalTheory.GaussTransport.iteratedDeriv_cexp_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:53:55.869058+00:00
-- url     : https://prove2.me/theorems/66b3c82c-a402-42e6-8c79-efb8c25d3a76
-- title:
--   Gauss Transport: iterated Deriv cexp mul
-- statement:
--   The Gauss Transport construction uses the iterated Deriv cexp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzDensityTransportLinearEquivChirp.lean#L6-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzDensityTransportLinearEquivChirp.lean#L6-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzDensityTransportLinearEquivChirp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GaussTransport

theorem GlobalTheory.GaussTransport.iteratedDeriv_cexp_mul (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (a * y)) = fun y : ℝ => a ^ n * Complex.exp (a * y) := by sorry
