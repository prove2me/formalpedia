-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGen_mem_of_homog_mem_iSup
-- name    : GlobalTheory.ThetaGen.mem_of_homog_mem_iSup
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:06:13.261129+00:00
-- url     : https://prove2.me/theorems/ad5f90bc-aa20-4325-b035-d0d783b2922d
-- title:
--   Theta Gen: mem of homog mem i Sup
-- statement:
--   The Theta Gen construction uses the mem of homog mem i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsHomogeneousOfMemSpanPow.lean#L28-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsHomogeneousOfMemSpanPow.lean#L28-L59

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
variable {X : Type}

theorem GlobalTheory.ThetaGen.mem_of_homog_mem_iSup (T : ℕ → Submodule ℂ (X → ℂ)) (d : ℕ) (f : X → ℂ)
    (h : homog d f ∈ ⨆ k, (T k).map (homogL k)) : f ∈ T d := by sorry
