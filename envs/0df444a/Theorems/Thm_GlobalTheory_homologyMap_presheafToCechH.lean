-- Prove2me | Theorems.Thm_GlobalTheory_homologyMap_presheafToCechH
-- name    : GlobalTheory.homologyMap_presheafToCechH
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:50:14.528989+00:00
-- url     : https://prove2.me/theorems/8b3a6ffc-8a1b-4881-accb-7350c0dd073e
-- title:
--   Global Theory: homology Map presheaf To Cech H
-- statement:
--   The Global Theory construction uses the homology Map presheaf To Cech H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L343-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L343-L347

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
variable {P}

theorem GlobalTheory.homologyMap_presheafToCechH (φ : P ⟶ Q) (x : P.obj (op V)) :
    (HomologicalComplex.homologyMap (cechComplexMap (presheafCubeMap V U φ)) 0).hom
      (presheafToCechH P V U x) = presheafToCechH Q V U ((φ.app (op V)).hom x) := by sorry
