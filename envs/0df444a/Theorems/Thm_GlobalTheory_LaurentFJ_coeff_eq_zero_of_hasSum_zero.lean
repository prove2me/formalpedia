-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFJ_coeff_eq_zero_of_hasSum_zero
-- name    : GlobalTheory.LaurentFJ.coeff_eq_zero_of_hasSum_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:04:35.822941+00:00
-- url     : https://prove2.me/theorems/182a5fd6-05c9-4ef5-a9ea-af7eaa63f784
-- title:
--   Laurent FJ: coeff eq zero of has Sum zero
-- statement:
--   The Laurent FJ construction uses the coeff eq zero of has Sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CoeffEqZeroOfHasSumZero.lean#L12-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CoeffEqZeroOfHasSumZero.lean#L12-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CoeffEqZeroOfHasSumZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFJ
open Complex ReciprocityTheory.ChartRestriction.G.FD
noncomputable section

theorem GlobalTheory.LaurentFJ.coeff_eq_zero_of_hasSum_zero (d : ℤ → ℂ)
    (h : ∀ t : ℝ, HasSum (fun k : ℤ => d k * cexp (2 * Real.pi * I * t) ^ k) 0) (j : ℤ) :
    d j = 0 := by sorry
