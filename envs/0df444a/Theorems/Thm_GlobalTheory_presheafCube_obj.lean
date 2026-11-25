-- Prove2me | Theorems.Thm_GlobalTheory_presheafCube_obj
-- name    : GlobalTheory.presheafCube_obj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:56:05.553675+00:00
-- url     : https://prove2.me/theorems/a74b45b0-a03c-4dd2-9ed9-349519f7cc25
-- title:
--   Global Theory: presheaf Cube obj
-- statement:
--   The Global Theory construction uses the presheaf Cube obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L166-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L166-L167

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

theorem GlobalTheory.presheafCube_obj (s : Finset ι) :
    (presheafCube P V U).obj s = P.obj (op (cechOpen V U s)) := by sorry
