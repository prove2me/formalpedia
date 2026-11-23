-- Prove2me | Theorems.Thm_GlobalTheory_HermModel_herm_smul_left
-- name    : GlobalTheory.HermModel.herm_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:32.017039+00:00
-- url     : https://prove2.me/theorems/136f2fd1-078b-494c-9df9-c1f544efdc66
-- title:
--   Herm Model: herm smul left
-- statement:
--   The Herm Model construction uses the herm smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean#L71-L75

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

theorem GlobalTheory.HermModel.herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (c • x) y = c * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y := by sorry
