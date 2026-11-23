-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_submatrix_mul_of_mem_blockUpper
-- name    : GroundTheory.Automorphic.Parabolic.submatrix_mul_of_mem_blockUpper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:02.084812+00:00
-- url     : https://prove2.me/theorems/eef064c0-9cc9-4d64-a98e-a5eab6ad6e2c
-- title:
--   Parabolic: submatrix mul of mem block Upper
-- statement:
--   The Parabolic construction uses the submatrix mul of mem block Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L91-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L91-L104

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (β γ : Fin n → ℕ)
variable {β γ}

theorem GroundTheory.Automorphic.Parabolic.submatrix_mul_of_mem_blockUpper {p : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (M : Matrix (Fin n) (Fin n) F) {ι : Type*} (c : ι → Fin n) (a : ℕ) :
    ((p : Matrix (Fin n) (Fin n) F) * M).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) c =
      (p : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))
          (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) *
        M.submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n)) c := by sorry
