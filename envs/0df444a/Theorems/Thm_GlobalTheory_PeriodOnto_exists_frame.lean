-- Prove2me | Theorems.Thm_GlobalTheory_PeriodOnto_exists_frame
-- name    : GlobalTheory.PeriodOnto.exists_frame
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:53.221676+00:00
-- url     : https://prove2.me/theorems/b183a374-cae9-45d6-b821-3e5b1e7167a3
-- title:
--   Period Onto: exists frame
-- statement:
--   The Period Onto construction uses the exists frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L53-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L53-L143

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

theorem GlobalTheory.PeriodOnto.exists_frame {r q : ℕ} (G M Mi : Matrix (Fin r) (Fin r) ℂ) (hM : M * Mi = 1)
    (hc : sgnMat r q * (Miᵀ * G * Mi.map conj) = (Miᵀ * G * Mi.map conj) * sgnMat r q)
    (hp : (sgnMat r q * (Miᵀ * G * Mi.map conj)).PosDef) :
    ∃ x : Matrix (Fin r) (Fin r) ℂ, x.det ≠ 0 ∧ (sgnMat r q * (xᵀ * G * x.map conj)).PosDef ∧
      ∀ (v : Fin r → ℂ) (a : Fin r),
        ((a : ℕ) < q → (v ᵥ* (G * x.map conj)) a = (M *ᵥ v) a) ∧
        (¬ (a : ℕ) < q → (x⁻¹ *ᵥ v) a = (M *ᵥ v) a) := by sorry
