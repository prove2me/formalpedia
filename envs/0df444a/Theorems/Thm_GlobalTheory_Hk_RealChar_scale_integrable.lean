-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RealChar_scale_integrable
-- name    : GlobalTheory.Hk.RealChar.scale_integrable
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:37:11.477833+00:00
-- url     : https://prove2.me/theorems/108ec1fb-2247-40b0-9117-c1786bc25134
-- title:
--   Real Char: scale integrable
-- statement:
--   The Real Char construction uses the scale integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormRayClassFamilyFOneGeOfRealCharacter.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormRayClassFamilyFOneGeOfRealCharacter.lean#L80-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter
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
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar

theorem GlobalTheory.Hk.RealChar.scale_integrable {y n : ℝ} (hy : 0 < y) (hn : 0 < n) :
    IntegrableOn (fun w => Real.exp (-(y / w)) * Real.exp (-(w * n)) / w) (Set.Ioi 0) := by sorry
