-- Prove2me | Theorems.Thm_GlobalTheory_Cube_SemiHom_term_aug
-- name    : GlobalTheory.Cube.SemiHom.term_aug
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:17.176177+00:00
-- url     : https://prove2.me/theorems/364e5b93-a1d5-5d6d-9db9-ae7bbdfd665b
-- title:
--   Semi Hom: term aug
-- statement:
--   The Semi Hom construction uses the term aug property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L223-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L223-L224

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
omit [LinearOrder ι]

theorem GlobalTheory.Cube.SemiHom.term_aug (a : A.obj ∅) : ψ.term 1 (Cube.aug A a) = Cube.aug B (ψ.app ∅ a) := by sorry
