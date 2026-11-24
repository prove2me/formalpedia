-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RaySq_conv_eq
-- name    : GlobalTheory.Hk.RaySq.conv_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:36.042659+00:00
-- url     : https://prove2.me/theorems/753ad75b-7e1c-4b32-a803-e3cfa357b0d2
-- title:
--   Ray Sq: conv eq
-- statement:
--   The Ray Sq construction uses the conv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L192-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L192-L278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar
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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Hk.RaySq.conv_eq (F : Ideal (𝓞 K) → Ideal (𝓞 K) → ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2, F (I * J) J =
      ∑ C ∈ normEq K n, ∑ J ∈ dv C, F C J := by sorry
