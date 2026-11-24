-- Prove2me | Theorems.Thm_GlobalTheory_RadialIntegral_radial
-- name    : GlobalTheory.RadialIntegral.radial
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:00.97102+00:00
-- url     : https://prove2.me/theorems/04a29f84-c404-4681-a39b-b21564657d70
-- title:
--   Radial Integral: radial
-- statement:
--   The Radial Integral construction uses the radial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralComplexInvPowAddNormSq.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralComplexInvPowAddNormSq.lean#L29-L41

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

theorem GlobalTheory.RadialIntegral.radial (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal ((a ^ (m + 1))⁻¹ / (2 * (m + 1))) := by sorry
