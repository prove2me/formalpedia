-- Prove2me | Theorems.Thm_GlobalTheory_PeriodOnto_comm_sgnMat_iff
-- name    : GlobalTheory.PeriodOnto.comm_sgnMat_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:51:36.429297+00:00
-- url     : https://prove2.me/theorems/dd577cee-b42a-4157-9f76-46d687879f5e
-- title:
--   Period Onto: comm sgn Mat iff
-- statement:
--   The Period Onto construction uses the comm sgn Mat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L17-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L17-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto

theorem GlobalTheory.PeriodOnto.comm_sgnMat_iff {r q : ℕ} (X : Matrix (Fin r) (Fin r) ℂ) :
    sgnMat r q * X = X * sgnMat r q ↔
      ∀ a b : Fin r, ¬ (((a : ℕ) < q) ↔ ((b : ℕ) < q)) → X a b = 0 := by sorry
