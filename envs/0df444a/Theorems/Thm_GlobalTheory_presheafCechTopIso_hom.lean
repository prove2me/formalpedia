-- Prove2me | Theorems.Thm_GlobalTheory_presheafCechTopIso_hom
-- name    : GlobalTheory.presheafCechTopIso_hom
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:50:23.687146+00:00
-- url     : https://prove2.me/theorems/33300a1a-df13-599a-841e-f37f4486c4f0
-- title:
--   Global Theory: presheaf Cech Top Iso hom
-- statement:
--   The Global Theory construction uses the presheaf Cech Top Iso hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L307-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L307-L308

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
variable {V U}

theorem GlobalTheory.presheafCechTopIso_hom (h : ∀ i, U i ≤ V) : (presheafCechTopIso P h).hom =
    cechComplexMap (presheafCubeRes P (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)) := by sorry
