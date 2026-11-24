-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGen_differentiable_of_mem_adjoin
-- name    : GlobalTheory.ThetaGen.differentiable_of_mem_adjoin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:06:06.470938+00:00
-- url     : https://prove2.me/theorems/92f4dc7b-9af5-4adf-9c60-5f9952898184
-- title:
--   Theta Gen: differentiable of mem adjoin
-- statement:
--   The Theta Gen construction uses the differentiable of mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsHomogeneousOfMemSpanPow.lean#L206-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsHomogeneousOfMemSpanPow.lean#L206-L212

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.ThetaGen.differentiable_of_mem_adjoin {S : Set (E → ℂ)} (hS : ∀ F ∈ S, Differentiable ℂ F)
    {F : E → ℂ} (hF : F ∈ Algebra.adjoin ℂ S) : Differentiable ℂ F := by sorry
