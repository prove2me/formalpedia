-- Prove2me | Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_naturality
-- name    : GlobalTheory.Cube.SemiHom.homology_naturality
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:47.348262+00:00
-- url     : https://prove2.me/theorems/ee93b0d7-485e-4e39-b48c-eecedf93dbf3
-- title:
--   Semi Hom: homology naturality
-- statement:
--   The Semi Hom construction uses the homology naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L343-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L343-L363

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
open CategoryTheory Limits
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B)

theorem GlobalTheory.Cube.SemiHom.homology_naturality (ψ' : _root_.GlobalTheory.Cube.SemiHom f A' B') (α : A ⟶ A')
    (β : B ⟶ B')
    (h : ∀ s, s.Nonempty → ∀ x, ψ'.app s ((α.app s).hom x) =
      (β.app s).hom (ψ.app s x)) (p : ℕ)
    (x : (_root_.GlobalTheory.cechComplex A).homology p) :
    ψ'.homology p
        ((HomologicalComplex.homologyMap (_root_.GlobalTheory.cechComplexMap α) p).hom x) =
      (HomologicalComplex.homologyMap (_root_.GlobalTheory.cechComplexMap β) p).hom
        (ψ.homology p x) := by sorry
