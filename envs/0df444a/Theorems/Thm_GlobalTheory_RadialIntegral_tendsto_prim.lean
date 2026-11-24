-- Prove2me | Theorems.Thm_GlobalTheory_RadialIntegral_tendsto_prim
-- name    : GlobalTheory.RadialIntegral.tendsto_prim
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:17.289413+00:00
-- url     : https://prove2.me/theorems/04093b2f-5104-4fc4-a3c3-1b0b1854405c
-- title:
--   Radial Integral: tendsto prim
-- statement:
--   The Radial Integral construction uses the tendsto prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralComplexInvPowAddNormSq.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralComplexInvPowAddNormSq.lean#L21-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralComplexInvPowAddNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.RadialIntegral

theorem GlobalTheory.RadialIntegral.tendsto_prim (m : ℕ) (a : ℝ) :
    Tendsto (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1)))) atTop (𝓝 0) := by sorry
