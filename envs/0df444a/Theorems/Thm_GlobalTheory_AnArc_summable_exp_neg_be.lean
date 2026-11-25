-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_summable_exp_neg_be
-- name    : GlobalTheory.AnArc.summable_exp_neg_be
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:56:26.254787+00:00
-- url     : https://prove2.me/theorems/7321f911-9a43-4576-9851-a9157c3ed5f9
-- title:
--   An Arc: summable exp neg be
-- statement:
--   The An Arc construction uses the summable exp neg be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L94-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L94-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.summable_exp_neg_be {δ : ℝ} (hδ : 0 < δ) (D : ℝ) :
    Summable fun μ => Real.exp (-(δ * A.be μ μ) + D * A.size μ) := by sorry
