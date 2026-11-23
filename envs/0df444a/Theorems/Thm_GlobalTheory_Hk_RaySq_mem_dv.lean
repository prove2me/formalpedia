-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RaySq_mem_dv
-- name    : GlobalTheory.Hk.RaySq.mem_dv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:01:20.725504+00:00
-- url     : https://prove2.me/theorems/3278afdd-6249-4351-86dc-81775a9118c1
-- title:
--   Ray Sq: mem dv
-- statement:
--   The Ray Sq construction uses the mem dv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L22-L28

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

theorem GlobalTheory.Hk.RaySq.mem_dv {C J : Ideal (𝓞 K)} (hC : C ≠ 0) : J ∈ dv C ↔ J ∣ C := by sorry
