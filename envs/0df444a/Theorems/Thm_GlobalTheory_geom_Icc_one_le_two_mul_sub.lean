-- Prove2me | Theorems.Thm_GlobalTheory_geom_Icc_one_le_two_mul_sub
-- name    : GlobalTheory.geom_Icc_one_le_two_mul_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:54:05.255112+00:00
-- url     : https://prove2.me/theorems/5f6e7c81-745c-4a50-b8d3-847c0d8cf872
-- title:
--   Global Theory: geom Icc one le two mul sub
-- statement:
--   The Global Theory construction uses the geom Icc one le two mul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeomIccOneLeTwoMulSub.lean#L8-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeomIccOneLeTwoMulSub.lean#L8-L16

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeomIccOneLeTwoMulSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory

theorem GlobalTheory.geom_Icc_one_le_two_mul_sub (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (N : ℕ) :
    ∑ i ∈ Icc 1 N, r ^ i ≤ 2 * r - 2 * r ^ (N + 1) := by sorry
