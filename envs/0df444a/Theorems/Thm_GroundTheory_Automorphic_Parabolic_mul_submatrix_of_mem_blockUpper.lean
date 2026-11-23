-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mul_submatrix_of_mem_blockUpper
-- name    : GroundTheory.Automorphic.Parabolic.mul_submatrix_of_mem_blockUpper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:04.460169+00:00
-- url     : https://prove2.me/theorems/ccd4a8a2-2967-4c59-8c21-a500ee56128c
-- title:
--   Parabolic: mul submatrix of mem block Upper
-- statement:
--   The Parabolic construction uses the mul submatrix of mem block Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L106-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L106-L119

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

theorem GroundTheory.Automorphic.Parabolic.mul_submatrix_of_mem_blockUpper {q : GL (Fin n) F} (hq : q ∈ blockUpper F n γ)
    (M : Matrix (Fin n) (Fin n) F) {ι : Type*} (r : ι → Fin n) (b : ℕ) :
    (M * (q : Matrix (Fin n) (Fin n) F)).submatrix r (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) =
      M.submatrix r (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) *
        (q : Matrix (Fin n) (Fin n) F).submatrix (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))
          (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) := by sorry
