-- Prove2me | Theorems.Thm_GlobalTheory_isIso_cechAugHomology_presheafCube
-- name    : GlobalTheory.isIso_cechAugHomology_presheafCube
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:47.710868+00:00
-- url     : https://prove2.me/theorems/128bef12-77b7-4c61-a8ba-0371e51d91de
-- title:
--   Global Theory: is Iso cech Aug Homology presheaf Cube
-- statement:
--   The Global Theory construction uses the is Iso cech Aug Homology presheaf Cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L416-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L416-L419

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
variable {T : TopCat.{w}} {ι : Type} {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  {V : Opens T} {U : ι → Opens T} (hc : V ≤ ⨆ i, U i)
include hP hc
variable [LinearOrder ι]

theorem GlobalTheory.isIso_cechAugHomology_presheafCube : IsIso (cechAugHomology (presheafCube P V U)) := by sorry
