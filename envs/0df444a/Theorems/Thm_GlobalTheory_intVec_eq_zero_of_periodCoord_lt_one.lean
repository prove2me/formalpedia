-- Prove2me | Theorems.Thm_GlobalTheory_intVec_eq_zero_of_periodCoord_lt_one
-- name    : GlobalTheory.intVec_eq_zero_of_periodCoord_lt_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:12.966851+00:00
-- url     : https://prove2.me/theorems/651686ed-17a9-450c-98b7-f6cb3cad5aea
-- title:
--   Global Theory: int Vec eq zero of period Coord lt one
-- statement:
--   The Global Theory construction uses the int Vec eq zero of period Coord lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L77-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L77-L91

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

theorem GlobalTheory.intVec_eq_zero_of_periodCoord_lt_one {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) (n n' : ι → ℤ)
    (h₁ : ∀ i, |periodCoordFst τ (τ *ᵥ ofIntVec n + ofIntVec n') i| < 1)
    (h₂ : ∀ i, |periodCoordSnd τ (τ *ᵥ ofIntVec n + ofIntVec n') i| < 1) :
    n = 0 ∧ n' = 0 := by sorry
