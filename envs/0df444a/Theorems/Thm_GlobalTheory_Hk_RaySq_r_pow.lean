-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RaySq_r_pow
-- name    : GlobalTheory.Hk.RaySq.r_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:59.219854+00:00
-- url     : https://prove2.me/theorems/4755a0ea-6653-4c98-90bc-beebbecf69b0
-- title:
--   Ray Sq: r pow
-- statement:
--   The Ray Sq construction uses the r pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L88-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L88-L98

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

theorem GlobalTheory.Hk.RaySq.r_pow (f : Ideal (𝓞 K) → ℝ) (hf : ∀ I J, f (I * J) = f I * f J) {P C : Ideal (𝓞 K)} (hP : Prime P) (hC : C ≠ 0)
    (hPC : ¬ P ∣ C) (k : ℕ) : r f (P ^ k * C) = (∑ i ∈ Finset.range (k + 1), f P ^ i) * r f C := by sorry
