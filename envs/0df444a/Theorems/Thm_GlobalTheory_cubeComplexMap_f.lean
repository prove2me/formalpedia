-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplexMap_f
-- name    : GlobalTheory.cubeComplexMap_f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:03.515271+00:00
-- url     : https://prove2.me/theorems/65cf1383-a8a6-49e7-9086-b76eab139a5c
-- title:
--   Global Theory: cube Complex Map f
-- statement:
--   The Global Theory construction uses the cube Complex Map f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L388-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L388-L389

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

theorem GlobalTheory.cubeComplexMap_f {A B : Cube.{v} ι R} (φ : A ⟶ B) (p : ℕ) :
    (cubeComplexMap φ).f p = ModuleCat.ofHom (Cube.termMap φ p) := by sorry
