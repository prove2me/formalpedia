-- Prove2me | Theorems.Thm_GlobalTheory_mulVec_periodCoordFst_add_periodCoordSnd
-- name    : GlobalTheory.mulVec_periodCoordFst_add_periodCoordSnd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:44.707144+00:00
-- url     : https://prove2.me/theorems/85a28946-9be5-4087-b029-b6bdc5b022e1
-- title:
--   Global Theory: mul Vec period Coord Fst add period Coord Snd
-- statement:
--   The Global Theory construction uses the mul Vec period Coord Fst add period Coord Snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L54-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L54-L67

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

theorem GlobalTheory.mulVec_periodCoordFst_add_periodCoordSnd {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) (w : ι → ℂ) :
    τ *ᵥ ofRealVec (periodCoordFst τ w) + ofRealVec (periodCoordSnd τ w) = w := by sorry
