-- Prove2me | Theorems.Thm_GlobalTheory_Cube_SemiHom_term_bijective
-- name    : GlobalTheory.Cube.SemiHom.term_bijective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:03.944109+00:00
-- url     : https://prove2.me/theorems/006e0cd5-622f-49e9-8517-ae50ebfa40b3
-- title:
--   Semi Hom: term bijective
-- statement:
--   The Semi Hom construction uses the term bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L232-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L232-L239

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
omit [LinearOrder ι]

theorem GlobalTheory.Cube.SemiHom.term_bijective
    (h : ∀ s : Finset ι, s.Nonempty → Function.Bijective (ψ.app s)) (p : ℕ) :
    Function.Bijective (ψ.term (p + 1)) := by sorry
