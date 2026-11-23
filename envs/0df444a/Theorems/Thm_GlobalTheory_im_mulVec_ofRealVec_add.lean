-- Prove2me | Theorems.Thm_GlobalTheory_im_mulVec_ofRealVec_add
-- name    : GlobalTheory.im_mulVec_ofRealVec_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:24.854856+00:00
-- url     : https://prove2.me/theorems/92fd3535-e344-4892-9a78-9b47e5a44c3d
-- title:
--   Global Theory: im mul Vec of Real Vec add
-- statement:
--   The Global Theory construction uses the im mul Vec of Real Vec add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L31-L34

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

theorem GlobalTheory.im_mulVec_ofRealVec_add (τ : Matrix ι ι ℂ) (u v : ι → ℝ) :
    (fun i => ((τ *ᵥ ofRealVec u + ofRealVec v) i).im) = τ.map Complex.im *ᵥ u := by sorry
