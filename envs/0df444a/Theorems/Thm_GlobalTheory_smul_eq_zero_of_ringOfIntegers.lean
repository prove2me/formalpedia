-- Prove2me | Theorems.Thm_GlobalTheory_smul_eq_zero_of_ringOfIntegers
-- name    : GlobalTheory.smul_eq_zero_of_ringOfIntegers
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:31.232806+00:00
-- url     : https://prove2.me/theorems/a2e7a147-da26-4013-97ec-4b4c5fa73233
-- title:
--   Global Theory: smul eq zero of ring Of Integers
-- statement:
--   The Global Theory construction uses the smul eq zero of ring Of Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankEqRankMulDegree.lean#L6-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankEqRankMulDegree.lean#L6-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankEqRankMulDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.smul_eq_zero_of_ringOfIntegers {F : Type} [Field F] [NumberField F] {M : Type}
    [AddCommGroup M] [Module (𝓞 F) M] [IsAddTorsionFree M] {a : 𝓞 F} (ha : a ≠ 0) {m : M}
    (h : a • m = 0) : m = 0 := by sorry
