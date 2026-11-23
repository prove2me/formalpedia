-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LogDeriv_summable_of_le
-- name    : GlobalTheory.Hk.LogDeriv.summable_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:58.448677+00:00
-- url     : https://prove2.me/theorems/3b312ce4-5727-46e3-aac3-a648083bd723
-- title:
--   Log Deriv: summable of le
-- statement:
--   The Log Deriv construction uses the summable of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyLogDerivReGtOne.lean#L112-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyLogDerivReGtOne.lean#L112-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOne
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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDeriv
open LSeries
open scoped LSeries.notation

theorem GlobalTheory.Hk.LogDeriv.summable_of_le {l : ℕ → ℂ} (hl : ∀ n, ‖l n‖ ≤ 2 * Λ n) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable l s := by sorry
