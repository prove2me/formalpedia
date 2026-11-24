-- Prove2me | Theorems.Thm_GlobalTheory_HermModel_herm_sub_left
-- name    : GlobalTheory.HermModel.herm_sub_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:19:06.750309+00:00
-- url     : https://prove2.me/theorems/f0adcad6-8f90-47cf-9040-d82996da38df
-- title:
--   Herm Model: herm sub left
-- statement:
--   The Herm Model construction uses the herm sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean#L63-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.HermModel.herm_sub_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (x - x') y = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y - _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x' y := by sorry
