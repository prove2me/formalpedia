-- Prove2me | Theorems.Thm_GlobalTheory_IntegerScalarIntegral_exists_int_smul_integral
-- name    : GlobalTheory.IntegerScalarIntegral.exists_int_smul_integral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:23.602034+00:00
-- url     : https://prove2.me/theorems/8fdcb15e-5ede-47e4-a34f-00d3b4fbf98c
-- title:
--   Integer Scalar Integral: exists int smul integral
-- statement:
--   The Integer Scalar Integral construction uses the exists int smul integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIntSmulIntegral.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIntSmulIntegral.lean#L9-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntSmulIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IntegerScalarIntegral
open NumberField

theorem GlobalTheory.IntegerScalarIntegral.exists_int_smul_integral {K : Type u_1} [Field K] [NumberField K] (c : K) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • c) := by sorry
