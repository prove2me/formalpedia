-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFJ_hasSum_fiber_of_hasSum_line
-- name    : GlobalTheory.LaurentFJ.hasSum_fiber_of_hasSum_line
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:04:23.445341+00:00
-- url     : https://prove2.me/theorems/04ed95b3-5fce-4c8b-b8a8-37983408f122
-- title:
--   Laurent FJ: has Sum fiber of has Sum line
-- statement:
--   The Laurent FJ construction uses the has Sum fiber of has Sum line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CoeffEqZeroOfHasSumZero.lean#L55-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CoeffEqZeroOfHasSumZero.lean#L55-L87

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

theorem GlobalTheory.LaurentFJ.hasSum_fiber_of_hasSum_line {ι : Type*} (c : ι → ℂ) (n : ι → ℤ) (a : ℤ → ℂ) (y : ℝ)
    (f : ℝ → ℂ)
    (ha : ∀ t : ℝ, HasSum (fun k : ℤ => a k * cexp (2 * Real.pi * I * (t + y * I)) ^ k) (f t))
    (hc : ∀ t : ℝ, HasSum (fun i => c i * cexp (2 * Real.pi * I * (t + y * I)) ^ n i) (f t))
    (j : ℤ) : HasSum (fun i : {i // n i = j} => c i) (a j) := by sorry
