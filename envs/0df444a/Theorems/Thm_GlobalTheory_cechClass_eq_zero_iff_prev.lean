-- Prove2me | Theorems.Thm_GlobalTheory_cechClass_eq_zero_iff_prev
-- name    : GlobalTheory.cechClass_eq_zero_iff_prev
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:40.033651+00:00
-- url     : https://prove2.me/theorems/0d215250-4174-43c1-b65c-43d5f36ce072
-- title:
--   Global Theory: cech Class eq zero iff prev
-- statement:
--   The Global Theory construction uses the cech Class eq zero iff prev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L41-L50

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

theorem GlobalTheory.cechClass_eq_zero_iff_prev (A : Cube.{v} ι R) (q p : ℕ)
    (h : (ComplexShape.up ℕ).prev p = q) (x : LinearMap.ker (Cube.d A (p + 1))) :
    cechClass A p x = 0 ↔ ∃ y, ((cechComplex A).d q p).hom y = x.1 := by sorry
