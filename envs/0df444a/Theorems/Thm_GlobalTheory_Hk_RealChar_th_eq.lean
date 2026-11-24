-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RealChar_th_eq
-- name    : GlobalTheory.Hk.RealChar.th_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:36:11.054644+00:00
-- url     : https://prove2.me/theorems/eda8d8ca-7ae7-49db-9985-292f68936eea
-- title:
--   Real Char: th eq
-- statement:
--   The Real Char construction uses the th eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormRayClassFamilyFOneGeOfRealCharacter.lean#L336-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormRayClassFamilyFOneGeOfRealCharacter.lean#L336-L341

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

theorem GlobalTheory.Hk.RealChar.th_eq {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} (h : χ * χ = 1) (t : ℝ) :
    ∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = (th (bRe 𝓕 χ) t : ℂ) := by sorry
