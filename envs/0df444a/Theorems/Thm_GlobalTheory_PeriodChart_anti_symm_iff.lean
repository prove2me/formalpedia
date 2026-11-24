-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_anti_symm_iff
-- name    : GlobalTheory.PeriodChart.anti_symm_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:42:52.929785+00:00
-- url     : https://prove2.me/theorems/75199612-581b-445c-b6b9-83ed14c34fd5
-- title:
--   Period Chart: anti symm iff
-- statement:
--   The Period Chart construction uses the anti symm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L290-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L290-L311

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}

theorem GlobalTheory.PeriodChart.anti_symm_iff (G Z : Matrix (Fin g) (Fin g) ℂ) :
    (∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z) ↔ (Gᵀ * Z)ᵀ = Gᵀ * Z := by sorry
