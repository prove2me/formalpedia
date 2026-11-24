-- Prove2me | Theorems.Thm_GlobalTheory_mertens_first_vonMangoldt
-- name    : GlobalTheory.mertens_first_vonMangoldt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:53:17.509626+00:00
-- url     : https://prove2.me/theorems/9f31350a-918e-434a-93da-0ee10e5eef1e
-- title:
--   Global Theory: mertens first von Mangoldt
-- statement:
--   The Global Theory construction uses the mertens first von Mangoldt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LogFactorialEqSumVonMangoldtMulDiv.lean#L59-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LogFactorialEqSumVonMangoldtMulDiv.lean#L59-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LogFactorialEqSumVonMangoldtMulDiv
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

theorem GlobalTheory.mertens_first_vonMangoldt :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ y : ℝ, 1 ≤ y →
      |∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) - Real.log y| ≤ CM := by sorry
