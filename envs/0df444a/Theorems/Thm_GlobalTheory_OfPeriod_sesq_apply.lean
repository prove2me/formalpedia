-- Prove2me | Theorems.Thm_GlobalTheory_OfPeriod_sesq_apply
-- name    : GlobalTheory.OfPeriod.sesq_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:51.870871+00:00
-- url     : https://prove2.me/theorems/63d914c7-ce8c-4ec0-85af-23d243ec6078
-- title:
--   Of Period: sesq apply
-- statement:
--   The Of Period construction uses the sesq apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L18-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex

theorem GlobalTheory.OfPeriod.sesq_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : sesq Hm z w = hermForm Hm z w := by sorry
