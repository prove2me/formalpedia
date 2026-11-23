-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RaySq_mem_normEq
-- name    : GlobalTheory.Hk.RaySq.mem_normEq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:01:58.60482+00:00
-- url     : https://prove2.me/theorems/7a6f75c1-5ecd-458c-8c2a-cdf4049c809a
-- title:
--   Ray Sq: mem norm Eq
-- statement:
--   The Ray Sq construction uses the mem norm Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L16-L17

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

theorem GlobalTheory.Hk.RaySq.mem_normEq {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ normEq K n ↔ Ideal.absNorm I = n := by sorry
