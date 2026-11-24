-- Prove2me | Theorems.Thm_GlobalTheory_mulVec_ofRealVec_add_mem_span_periodLattice
-- name    : GlobalTheory.mulVec_ofRealVec_add_mem_span_periodLattice
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:38.756917+00:00
-- url     : https://prove2.me/theorems/75577977-9b57-44c2-9814-73caa737014b
-- title:
--   Global Theory: mul Vec of Real Vec add mem span period Lattice
-- statement:
--   The Global Theory construction uses the mul Vec of Real Vec add mem span period Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L126-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L126-L143

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
omit [DecidableEq ι]

theorem GlobalTheory.mulVec_ofRealVec_add_mem_span_periodLattice (τ : Matrix ι ι ℂ) (u v : ι → ℝ) :
    τ *ᵥ ofRealVec u + ofRealVec v ∈
      Submodule.span ℝ (periodLattice τ : Set (ι → ℂ)) := by sorry
