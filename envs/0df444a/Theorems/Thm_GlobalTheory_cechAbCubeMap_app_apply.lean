-- Prove2me | Theorems.Thm_GlobalTheory_cechAbCubeMap_app_apply
-- name    : GlobalTheory.cechAbCubeMap_app_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:50:50.622521+00:00
-- url     : https://prove2.me/theorems/46e34d27-b8d0-4fab-971f-4574931e2cbd
-- title:
--   Global Theory: cech Ab Cube Map app apply
-- statement:
--   The Global Theory construction uses the cech Ab Cube Map app apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L464-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L464-L465

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
variable {P}

theorem GlobalTheory.cechAbCubeMap_app_apply (φ : P ⟶ Q) (s : Finset ι) (x : P.obj (op (cechOpen V U s))) :
    ((cechAbCubeMap V U φ).app s).hom x = φ.app (op (cechOpen V U s)) x := by sorry

attribute [defeq] GlobalTheory.cechAbCubeMap_app_apply
