-- Prove2me | Theorems.Thm_GlobalTheory_cechAugHomology_apply
-- name    : GlobalTheory.cechAugHomology_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:22.024512+00:00
-- url     : https://prove2.me/theorems/4d3cca76-b38e-47d0-a32d-24c2f6690f5b
-- title:
--   Global Theory: cech Aug Homology apply
-- statement:
--   The Global Theory construction uses the cech Aug Homology apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L160-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L160-L174

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
open CategoryTheory Limits
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]

theorem GlobalTheory.cechAugHomology_apply (A : _root_.GlobalTheory.Cube.{v} ι R) (a : A.obj ∅) :
    (_root_.GlobalTheory.cechAugHomology A).hom a =
      _root_.GlobalTheory.cechClass A 0
        ⟨_root_.GlobalTheory.Cube.aug A a, _root_.GlobalTheory.Cube.d_aug A a⟩ := by sorry
