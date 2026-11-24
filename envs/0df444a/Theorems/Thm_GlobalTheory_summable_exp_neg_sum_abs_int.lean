-- Prove2me | Theorems.Thm_GlobalTheory_summable_exp_neg_sum_abs_int
-- name    : GlobalTheory.summable_exp_neg_sum_abs_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:34.58438+00:00
-- url     : https://prove2.me/theorems/6fd99e87-9dd1-44db-8f7d-d1a5919669d0
-- title:
--   Global Theory: summable exp neg sum abs int
-- statement:
--   The Global Theory construction uses the summable exp neg sum abs int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L14-L22

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

theorem GlobalTheory.summable_exp_neg_sum_abs_int {ι : Type} [Fintype ι] :
    Summable fun m : ι → ℤ => Real.exp (-∑ i, |(m i : ℝ)|) := by sorry
