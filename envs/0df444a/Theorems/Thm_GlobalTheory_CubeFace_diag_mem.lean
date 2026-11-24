-- Prove2me | Theorems.Thm_GlobalTheory_CubeFace_diag_mem
-- name    : GlobalTheory.CubeFace.diag_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:17.346346+00:00
-- url     : https://prove2.me/theorems/4661084e-8713-4ec4-a5df-7b31e1f62b58
-- title:
--   Cube Face: diag mem
-- statement:
--   The Cube Face construction uses the diag mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L135-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L135-L141

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

theorem GlobalTheory.CubeFace.diag_mem {V ι : Type*} [AddCommGroup V] [Module ℂ V] (W : ι → Set V) {a b d o : ι}
    {z : V} (ha : z ∈ W a) (hb : -z ∈ W b) (hd : (2 : ℂ) • z ∈ W d) (ho : (0 : V) ∈ W o)
    (J : Finset (Fin 3)) :
    ∑ i ∈ J, (![z, z, -z] : Fin 3 → V) i ∈ W (diagChart a b d o J) := by sorry
