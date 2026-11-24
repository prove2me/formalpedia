-- Prove2me | Theorems.Thm_GlobalTheory_app_presheafRes
-- name    : GlobalTheory.app_presheafRes
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:50:09.160781+00:00
-- url     : https://prove2.me/theorems/2bd13ed7-ae6c-42d0-a9ea-fa189e809e46
-- title:
--   Global Theory: app presheaf Res
-- statement:
--   The Global Theory construction uses the app presheaf Res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L158-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L158-L160

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
variable {P}

theorem GlobalTheory.app_presheafRes (φ : P ⟶ Q) {W W' : Opens T} (h : W' ≤ W) (x : P.obj (op W)) :
    (φ.app (op W')).hom (presheafRes P h x) = presheafRes Q h ((φ.app (op W)).hom x) := by sorry
