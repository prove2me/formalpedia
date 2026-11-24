-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RealChar_summable_th
-- name    : GlobalTheory.Hk.RealChar.summable_th
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:37:01.941235+00:00
-- url     : https://prove2.me/theorems/6ba83442-3cb1-47bc-a55b-b515080bb794
-- title:
--   Real Char: summable th
-- statement:
--   The Real Char construction uses the summable th property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormRayClassFamilyFOneGeOfRealCharacter.lean#L100-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormRayClassFamilyFOneGeOfRealCharacter.lean#L100-L106

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

theorem GlobalTheory.Hk.RealChar.summable_th {a : ℕ → ℝ} {D : ℝ} (ha : ∀ n, |a n| ≤ D * n) {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => ‖a n * Real.exp (-(t * n))‖ := by sorry
