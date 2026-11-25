-- Prove2me | Theorems.Thm_GlobalTheory_Cube_d_two_apply_triple
-- name    : GlobalTheory.Cube.d_two_apply_triple
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:50.968932+00:00
-- url     : https://prove2.me/theorems/37774ed4-57a4-4d14-9220-297c22c8c932
-- title:
--   Cube: d two apply triple
-- statement:
--   The Cube construction uses the d two apply triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoboundaryOfFractionCocycleHomogeneousIdea.lean#L43-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoboundaryOfFractionCocycleHomogeneousIdea.lean#L43-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdea
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id


set_option autoImplicit false
open MvPolynomial DirectSum
open GlobalTheory

theorem GlobalTheory.Cube.d_two_apply_triple {ι : Type} [LinearOrder ι] {R : Type*} [Ring R]
    (A : Cube ι R) (x : Cube.Term A 2) {i j l : ι} (hij : i < j) (hjl : j < l) :
    Cube.d A 2 x ⟨{i, j, l}, by rw [Finset.card_eq_three]; exact ⟨i, j, l, hij.ne, (hij.trans hjl).ne, hjl.ne, rfl⟩⟩ =
      Cube.res A (by intro k; simp; tauto) (x ⟨{j, l}, Finset.card_pair hjl.ne⟩) -
        Cube.res A (by intro k; simp; tauto) (x ⟨{i, l}, Finset.card_pair (hij.trans hjl).ne⟩) +
        Cube.res A (by intro k; simp; tauto) (x ⟨{i, j}, Finset.card_pair hij.ne⟩) := by sorry
