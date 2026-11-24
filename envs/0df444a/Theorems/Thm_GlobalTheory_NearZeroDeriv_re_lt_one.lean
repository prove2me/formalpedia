-- Prove2me | Theorems.Thm_GlobalTheory_NearZeroDeriv_re_lt_one
-- name    : GlobalTheory.NearZeroDeriv.re_lt_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:59.599616+00:00
-- url     : https://prove2.me/theorems/3f2dfaac-470e-4585-a592-70d2a46ebfae
-- title:
--   Near Zero Deriv: re lt one
-- statement:
--   The Near Zero Deriv construction uses the re lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLargeVonMangoldtLogPowerSeriesNearZero.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLargeVonMangoldtLogPowerSeriesNearZero.lean#L116-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficientsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLargeVonMangoldtLogPowerSeriesNearZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.NearZeroDeriv

theorem GlobalTheory.NearZeroDeriv.re_lt_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {c w : ℂ} {R : ℝ}
    (hw : w ∈ zerosDisc χ c R) : w.re < 1 := by sorry
