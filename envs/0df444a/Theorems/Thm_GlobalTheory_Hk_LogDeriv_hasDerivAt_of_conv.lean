-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LogDeriv_hasDerivAt_of_conv
-- name    : GlobalTheory.Hk.LogDeriv.hasDerivAt_of_conv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:08.412799+00:00
-- url     : https://prove2.me/theorems/11647e32-08f0-4440-90ff-fb1ce961e8f9
-- title:
--   Log Deriv: has Deriv At of conv
-- statement:
--   The Log Deriv construction uses the has Deriv At of conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyLogDerivReGtOne.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyLogDerivReGtOne.lean#L20-L26

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

theorem GlobalTheory.Hk.LogDeriv.hasDerivAt_of_conv {a l : ℕ → ℂ} (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hl : ∀ s : ℂ, 1 < s.re → LSeriesSummable l s)
    (hc : ∀ n : ℕ, n ≠ 0 → Complex.log n * a n = (l ⍟ a) n) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (LSeries a) (-(LSeries l s * LSeries a s)) s := by sorry
