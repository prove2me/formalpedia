-- Prove2me | Theorems.Thm_GlobalTheory_HermModel_eq_zero_of_herm_eq_zero
-- name    : GlobalTheory.HermModel.eq_zero_of_herm_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:19:34.167081+00:00
-- url     : https://prove2.me/theorems/fab3a61d-d2f6-4d04-afe2-56fb4325565c
-- title:
--   Herm Model: eq zero of herm eq zero
-- statement:
--   The Herm Model construction uses the eq zero of herm eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean#L106-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean#L106-L113

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

theorem GlobalTheory.HermModel.eq_zero_of_herm_eq_zero {G : Matrix (Fin r) (Fin r) E}
    (hG : G.det ≠ 0) {w : Fin r → E} (hw : ∀ u, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G w u = 0) : w = 0 := by sorry
