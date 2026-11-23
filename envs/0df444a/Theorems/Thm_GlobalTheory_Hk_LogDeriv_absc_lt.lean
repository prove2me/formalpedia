-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LogDeriv_absc_lt
-- name    : GlobalTheory.Hk.LogDeriv.absc_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:47.978074+00:00
-- url     : https://prove2.me/theorems/0bc56b51-33d2-4df7-865e-6c5e20b53c4d
-- title:
--   Log Deriv: absc lt
-- statement:
--   The Log Deriv construction uses the absc lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyLogDerivReGtOne.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassFamilyLogDerivReGtOne.lean#L13-L18

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

theorem GlobalTheory.Hk.LogDeriv.absc_lt {a : ℕ → ℂ} (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s) {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv a < s.re := by sorry
