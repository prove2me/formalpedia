-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isUnit_det_submatrix_of_mem_blockUpper
-- name    : GroundTheory.Automorphic.Parabolic.isUnit_det_submatrix_of_mem_blockUpper
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:28.269102+00:00
-- url     : https://prove2.me/theorems/b7211564-e52e-40a6-8293-1e0852d8b12d
-- title:
--   Parabolic: is Unit det submatrix of mem block Upper
-- statement:
--   The Parabolic construction uses the is Unit det submatrix of mem block Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L121-L129

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

theorem GroundTheory.Automorphic.Parabolic.isUnit_det_submatrix_of_mem_blockUpper {p : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (a : ℕ) :
    IsUnit ((p : Matrix (Fin n) (Fin n) F).submatrix (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))
      (fun i : {i : Fin n // a ≤ β i} => (i : Fin n))).det := by sorry
