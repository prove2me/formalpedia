-- Prove2me | Theorems.Thm_GlobalTheory_homologyMap_res_presheafToCechH
-- name    : GlobalTheory.homologyMap_res_presheafToCechH
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:19.907825+00:00
-- url     : https://prove2.me/theorems/8242b00e-a7ac-41b7-a5ea-5c01ddce1300
-- title:
--   Global Theory: homology Map res presheaf To Cech H
-- statement:
--   The Global Theory construction uses the homology Map res presheaf To Cech H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L351-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L351-L358

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

theorem GlobalTheory.homologyMap_res_presheafToCechH {V' : Opens T} {U' : ι → Opens T}
    (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) (hV : V' ≤ V) (x : P.obj (op V)) :
    (HomologicalComplex.homologyMap (cechComplexMap (presheafCubeRes P h)) 0).hom
      (presheafToCechH P V U x) = presheafToCechH P V' U' (presheafRes P hV x) := by sorry
