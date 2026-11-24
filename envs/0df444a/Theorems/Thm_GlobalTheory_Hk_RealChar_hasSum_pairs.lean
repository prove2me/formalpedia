-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RealChar_hasSum_pairs
-- name    : GlobalTheory.Hk.RealChar.hasSum_pairs
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:36:55.713013+00:00
-- url     : https://prove2.me/theorems/a729d59d-9a55-493c-a815-4d4901fe2a3f
-- title:
--   Real Char: has Sum pairs
-- statement:
--   The Real Char construction uses the has Sum pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormRayClassFamilyFOneGeOfRealCharacter.lean#L108-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormRayClassFamilyFOneGeOfRealCharacter.lean#L108-L174

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

theorem GlobalTheory.Hk.RealChar.hasSum_pairs {a b : ℕ → ℝ} {D : ℝ} (ha : ∀ n, |a n| ≤ D * n) (hb : ∀ n, |b n| ≤ D * n)
    {v : ℝ} (hv : 0 < v) :
    HasSum (fun p : ℕ × ℕ => a p.1 * b p.2 * besW (v * p.1 * p.2))
      (∫ w in Set.Ioi (0 : ℝ), th a (v / w) * th b w / w) := by sorry
