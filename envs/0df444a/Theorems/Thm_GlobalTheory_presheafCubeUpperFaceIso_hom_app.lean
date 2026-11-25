-- Prove2me | Theorems.Thm_GlobalTheory_presheafCubeUpperFaceIso_hom_app
-- name    : GlobalTheory.presheafCubeUpperFaceIso_hom_app
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:51.545723+00:00
-- url     : https://prove2.me/theorems/744de796-93cf-5575-8c04-e50afcbf368b
-- title:
--   Global Theory: presheaf Cube Upper Face Iso hom app
-- statement:
--   The Global Theory construction uses the presheaf Cube Upper Face Iso hom app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L264-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L264-L266

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

theorem GlobalTheory.presheafCubeUpperFaceIso_hom_app (s : Finset κ) :
    ((presheafCubeUpperFaceIso P V U e i).hom.app s).hom =
      presheafRes P (cechOpen_insert_map V U e.toEmbedding i s).ge := by sorry
