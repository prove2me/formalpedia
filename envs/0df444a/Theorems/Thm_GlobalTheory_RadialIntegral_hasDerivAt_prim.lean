-- Prove2me | Theorems.Thm_GlobalTheory_RadialIntegral_hasDerivAt_prim
-- name    : GlobalTheory.RadialIntegral.hasDerivAt_prim
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:12:19.01283+00:00
-- url     : https://prove2.me/theorems/057ab493-d743-48fe-91ba-fef8b3c93146
-- title:
--   Radial Integral: has Deriv At prim
-- statement:
--   The Radial Integral construction uses the has Deriv At prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralComplexInvPowAddNormSq.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralComplexInvPowAddNormSq.lean#L7-L19

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

theorem GlobalTheory.RadialIntegral.hasDerivAt_prim (m : ℕ) (a : ℝ) (ha : 0 < a) (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1))))
      (r * ((a + r ^ 2) ^ (m + 2))⁻¹) r := by sorry
