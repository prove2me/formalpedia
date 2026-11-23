-- Prove2me | Theorems.Thm_GlobalTheory_HermModel_herm_add_right
-- name    : GlobalTheory.HermModel.herm_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:44.803386+00:00
-- url     : https://prove2.me/theorems/1a33c476-d704-4c80-b915-1de7e878b191
-- title:
--   Herm Model: herm add right
-- statement:
--   The Herm Model construction uses the herm add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean#L80-L83

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

theorem GlobalTheory.HermModel.herm_add_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x (y + y') = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y + _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y' := by sorry
