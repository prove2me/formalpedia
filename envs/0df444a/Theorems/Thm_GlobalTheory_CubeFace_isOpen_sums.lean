-- Prove2me | Theorems.Thm_GlobalTheory_CubeFace_isOpen_sums
-- name    : GlobalTheory.CubeFace.isOpen_sums
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:18.771694+00:00
-- url     : https://prove2.me/theorems/b43949de-1f31-4e1f-9802-366c61fe8ff0
-- title:
--   Cube Face: is Open sums
-- statement:
--   The Cube Face construction uses the is Open sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L155-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L155-L160

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

theorem GlobalTheory.CubeFace.isOpen_sums {g : ℕ} {ι : Type} (W : ι → Set (Fin g → ℂ)) (hW : ∀ i, IsOpen (W i))
    (j : Finset (Fin 3) → ι) :
    IsOpen {x : Fin 3 → Fin g → ℂ | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)} := by sorry
