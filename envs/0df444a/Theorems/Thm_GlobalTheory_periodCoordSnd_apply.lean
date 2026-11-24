-- Prove2me | Theorems.Thm_GlobalTheory_periodCoordSnd_apply
-- name    : GlobalTheory.periodCoordSnd_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:55.254814+00:00
-- url     : https://prove2.me/theorems/94877c08-6880-40af-b589-31f992b4c41c
-- title:
--   Global Theory: period Coord Snd apply
-- statement:
--   The Global Theory construction uses the period Coord Snd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L48-L52

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

theorem GlobalTheory.periodCoordSnd_apply {τ : Matrix ι ι ℂ} (hτ : IsUnit (τ.map Complex.im).det)
    (u v : ι → ℝ) : periodCoordSnd τ (τ *ᵥ ofRealVec u + ofRealVec v) = v := by sorry
