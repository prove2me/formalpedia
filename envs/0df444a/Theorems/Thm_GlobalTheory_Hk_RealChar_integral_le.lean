-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RealChar_integral_le
-- name    : GlobalTheory.Hk.RealChar.integral_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:37:19.545887+00:00
-- url     : https://prove2.me/theorems/ce1bfaf6-400b-43fe-bf9e-888cc840b82c
-- title:
--   Real Char: integral le
-- statement:
--   The Real Char construction uses the integral le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormRayClassFamilyFOneGeOfRealCharacter.lean#L255-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormRayClassFamilyFOneGeOfRealCharacter.lean#L255-L292

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

theorem GlobalTheory.Hk.RealChar.integral_le {P Q : ℝ → ℝ} (hP : Measurable P) (hQ : Measurable Q) {ρ E : ℝ} (hE : 0 ≤ E)
    (h1 : ∀ t, 0 < t → |P t - ρ / t| ≤ E * min t (1 / t))
    (h2 : ∀ t, 0 < t → |Q t| ≤ E * min t (1 / t)) (hi : IntegrableOn Q (Set.Ioi 0))
    {v : ℝ} (hv : 0 < v) :
    ∫ w in Set.Ioi (0 : ℝ), P (v / w) * Q w / w ≤
      ρ / v * (∫ w in Set.Ioi (0 : ℝ), Q w) + E ^ 2 * Real.sqrt v * ∫ w in Set.Ioi (0 : ℝ), wt w := by sorry
