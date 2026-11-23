-- Prove2me | Theorems.Thm_GlobalTheory_Cube_termMap_mem_ker
-- name    : GlobalTheory.Cube.termMap_mem_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:40.816606+00:00
-- url     : https://prove2.me/theorems/d7a98fe0-08e5-4d20-98cf-db32e88b8bc0
-- title:
--   Cube: term Map mem ker
-- statement:
--   The Cube construction uses the term Map mem ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L150-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean#L150-L155

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

theorem GlobalTheory.Cube.termMap_mem_ker {A B : _root_.GlobalTheory.Cube.{v} ι R} (φ : A ⟶ B) {p : ℕ}
    {x : _root_.GlobalTheory.Cube.Term A p}
    (h : x ∈ LinearMap.ker (_root_.GlobalTheory.Cube.d A p)) :
    _root_.GlobalTheory.Cube.termMap φ p x ∈ LinearMap.ker (_root_.GlobalTheory.Cube.d B p) := by sorry
