-- Prove2me | Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_restrictScalars_bijective
-- name    : GlobalTheory.Cube.SemiHom.homology_restrictScalars_bijective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:12.483943+00:00
-- url     : https://prove2.me/theorems/813abbd8-0a6f-5f31-8831-e2547750ea48
-- title:
--   Semi Hom: homology restrict Scalars bijective
-- statement:
--   The Semi Hom construction uses the homology restrict Scalars bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L397-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L397-L399

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
noncomputable section
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
open GlobalTheory.Cube GlobalTheory.Cube.SemiHom
variable {f : R →+* S} {A A' : Cube.{v} ι R} {B B' : Cube.{v'} ι S} (ψ : Cube.SemiHom f A B)

theorem GlobalTheory.Cube.SemiHom.homology_restrictScalars_bijective (f : R →+* S) (B : Cube.{v} ι S) (p : ℕ) :
    Function.Bijective ((restrictScalars f B).homology p) := by sorry
