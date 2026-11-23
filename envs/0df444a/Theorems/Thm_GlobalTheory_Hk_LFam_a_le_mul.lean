-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LFam_a_le_mul
-- name    : GlobalTheory.Hk.LFam.a_le_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:36.875852+00:00
-- url     : https://prove2.me/theorems/3e7e8ad6-23a0-4684-8f51-5fce4786f7a4
-- title:
--   LFam: a le mul
-- statement:
--   The LFam construction uses the a le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L129-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L129-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk

theorem GlobalTheory.Hk.LFam.a_le_mul (𝓕 : LFam) (g : 𝓕.G) (n : ℕ) : 𝓕.a g n ≤ 14 * n := by sorry
