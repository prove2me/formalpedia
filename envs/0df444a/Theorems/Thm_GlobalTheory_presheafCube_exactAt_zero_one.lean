-- Prove2me | Theorems.Thm_GlobalTheory_presheafCube_exactAt_zero_one
-- name    : GlobalTheory.presheafCube_exactAt_zero_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:49:57.918863+00:00
-- url     : https://prove2.me/theorems/0cb3cb4c-df44-49bc-a42e-ba07e0d46202
-- title:
--   Global Theory: presheaf Cube exact At zero one
-- statement:
--   The Global Theory construction uses the presheaf Cube exact At zero one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L421-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoCechComplexMapPresheafCubeRes.lean#L421-L423

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

theorem GlobalTheory.presheafCube_exactAt_zero_one :
    (cubeComplex (presheafCube P V U)).ExactAt 0 ∧ (cubeComplex (presheafCube P V U)).ExactAt 1 := by sorry
