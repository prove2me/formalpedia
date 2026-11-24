-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_perFactor_of_y_eq_zero
-- name    : GlobalTheory.AnArc.perFactor_of_y_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:58:07.2383+00:00
-- url     : https://prove2.me/theorems/dbe962f3-1f68-459b-b780-47e4a5e0ee69
-- title:
--   An Arc: per Factor of y eq zero
-- statement:
--   The An Arc construction uses the per Factor of y eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L141-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L141-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.perFactor_of_y_eq_zero (w : ℂ) {la : A.La} (h : la.y = 0) (v : A.V) : A.perFactor w la v = A.ah la.l v.2 := by sorry
