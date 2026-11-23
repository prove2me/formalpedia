-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RaySq_sum_aRay
-- name    : GlobalTheory.Hk.RaySq.sum_aRay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:15.073998+00:00
-- url     : https://prove2.me/theorems/d6b7a31a-2432-4433-9287-bfb6e989c57c
-- title:
--   Ray Sq: sum a Ray
-- statement:
--   The Ray Sq construction uses the sum a Ray property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L285-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConvRealChar.lean#L285-L307

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
variable {M : ℕ} (D : RayData K M)

theorem GlobalTheory.Hk.RaySq.sum_aRay (ε : D.G → ℝ) (n : ℕ) : ∑ g, ε g * aRay D g n = ∑ I ∈ normEq K n, chi D ε I := by sorry
