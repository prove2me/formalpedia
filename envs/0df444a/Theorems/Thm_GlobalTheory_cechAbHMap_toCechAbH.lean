-- Prove2me | Theorems.Thm_GlobalTheory_cechAbHMap_toCechAbH
-- name    : GlobalTheory.cechAbHMap_toCechAbH
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:50:01.15425+00:00
-- url     : https://prove2.me/theorems/aeb60c99-7e91-440e-aa98-443b0ce52a9f
-- title:
--   Global Theory: cech Ab HMap to Cech Ab H
-- statement:
--   The Global Theory construction uses the cech Ab HMap to Cech Ab H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L562-L564
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L562-L564

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
variable {T : Type w} [TopologicalSpace T] {ι : Type}
  (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) {Q Q' : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}}
  (V : Opens T) (U : ι → Opens T)
variable [LinearOrder ι]
variable {P}

theorem GlobalTheory.cechAbHMap_toCechAbH (φ : P ⟶ Q) (x : P.obj (op V)) :
    (cechAbHMap V U φ 0).hom (toCechAbH P V U x) = toCechAbH Q V U (φ.app (op V) x) := by sorry
