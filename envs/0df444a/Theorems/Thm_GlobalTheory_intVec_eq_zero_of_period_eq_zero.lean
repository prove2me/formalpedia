-- Prove2me | Theorems.Thm_GlobalTheory_intVec_eq_zero_of_period_eq_zero
-- name    : GlobalTheory.intVec_eq_zero_of_period_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:10.26964+00:00
-- url     : https://prove2.me/theorems/df346f7c-aa50-49e8-8d6b-85e332142b58
-- title:
--   Global Theory: int Vec eq zero of period eq zero
-- statement:
--   The Global Theory construction uses the int Vec eq zero of period eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L153-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L153-L158

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.intVec_eq_zero_of_period_eq_zero {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) (n n' : ι → ℤ)
    (h : τ *ᵥ ofIntVec n + ofIntVec n' = 0) : n = 0 ∧ n' = 0 := by sorry
