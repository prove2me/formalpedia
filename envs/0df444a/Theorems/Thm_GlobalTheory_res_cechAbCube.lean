-- Prove2me | Theorems.Thm_GlobalTheory_res_cechAbCube
-- name    : GlobalTheory.res_cechAbCube
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:50:30.421721+00:00
-- url     : https://prove2.me/theorems/84b51fc7-7293-4317-b81a-a41b4acf8214
-- title:
--   Global Theory: res cech Ab Cube
-- statement:
--   The Global Theory construction uses the res cech Ab Cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L453-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L453-L454

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

theorem GlobalTheory.res_cechAbCube {s t : Finset ι} (h : s ⊆ t) (x : P.obj (op (cechOpen V U s))) :
    Cube.res (cechAbCube P V U) h x = P.map (homOfLE (cechOpen_anti V U h)).op x := by sorry
