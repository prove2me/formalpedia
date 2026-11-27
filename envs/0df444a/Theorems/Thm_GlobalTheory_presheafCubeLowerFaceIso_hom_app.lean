-- Prove2me | Theorems.Thm_GlobalTheory_presheafCubeLowerFaceIso_hom_app
-- name    : GlobalTheory.presheafCubeLowerFaceIso_hom_app
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:49:52.865836+00:00
-- url     : https://prove2.me/theorems/aeef88e8-c541-572a-8e75-ec816270060c
-- title:
--   Global Theory: presheaf Cube Lower Face Iso hom app
-- statement:
--   The Global Theory construction uses the presheaf Cube Lower Face Iso hom app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L260-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L260-L262

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace Opposite
universe w v u
noncomputable section
open GlobalTheory
variable {T : Type w} [TopologicalSpace T] {ι κ : Type} {R : Type u} [Ring R]
variable (P : (Opens T)ᵒᵖ ⥤ ModuleCat.{v} R) {Q Q' : (Opens T)ᵒᵖ ⥤ ModuleCat.{v} R}
variable (V : Opens T) (U : ι → Opens T)
variable [LinearOrder ι]
variable [LinearOrder κ] (e : κ ↪o ι) (i : ι)

theorem GlobalTheory.presheafCubeLowerFaceIso_hom_app (s : Finset κ) :
    ((presheafCubeLowerFaceIso P V U e).hom.app s).hom =
      presheafRes P (cechOpen_map V U e.toEmbedding s).ge := by sorry
