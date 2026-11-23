-- Prove2me | Theorems.Thm_GlobalTheory_ofIntVec_eq_ofRealVec
-- name    : GlobalTheory.ofIntVec_eq_ofRealVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:28.517523+00:00
-- url     : https://prove2.me/theorems/3bb522a6-8122-42d3-84b1-9c5e98e4d358
-- title:
--   Global Theory: of Int Vec eq of Real Vec
-- statement:
--   The Global Theory construction uses the of Int Vec eq of Real Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L70-L71

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
omit [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.ofIntVec_eq_ofRealVec (n : ι → ℤ) : ofIntVec n = ofRealVec fun i => (n i : ℝ) := by sorry
