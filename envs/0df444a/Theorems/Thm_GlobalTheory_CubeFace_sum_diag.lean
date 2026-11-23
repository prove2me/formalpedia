-- Prove2me | Theorems.Thm_GlobalTheory_CubeFace_sum_diag
-- name    : GlobalTheory.CubeFace.sum_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:59:32.245519+00:00
-- url     : https://prove2.me/theorems/d117286b-d333-4c5f-a0d4-bdff92a8dc39
-- title:
--   Cube Face: sum diag
-- statement:
--   The Cube Face construction uses the sum diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L127-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L127-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace

theorem GlobalTheory.CubeFace.sum_diag {V : Type*} [AddCommGroup V] [Module ℂ V] (z : V) (J : Finset (Fin 3)) :
    ∑ a ∈ J, (![z, z, -z] : Fin 3 → V) a = diagChart z (-z) ((2 : ℂ) • z) 0 J := by sorry
