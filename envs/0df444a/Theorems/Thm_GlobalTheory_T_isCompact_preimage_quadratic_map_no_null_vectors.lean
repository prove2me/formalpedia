-- Prove2me | Theorems.Thm_GlobalTheory_T_isCompact_preimage_quadratic_map_no_null_vectors
-- name    : GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:21.296085+00:00
-- url     : https://prove2.me/theorems/7b4e34bf-a64b-4714-b2df-6ea7de8ee23c
-- title:
--   T: is Compact preimage quadratic map no null vectors
-- statement:
--   The T construction uses the is Compact preimage quadratic map no null vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCompactPreimageQuadraticMapNoNullVectorsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCompactPreimageQuadraticMapNoNullVectorsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactPreimageQuadraticMapNoNullVectors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactPreimageQuadraticMapNoNullVectorsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors : ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K], (∀ x : K, ‖star x‖ = ‖x‖) → ∀ (m : ℕ) (S : Submodule K (Matrix (Fin m) (Fin m) K)) (q : Matrix (Fin m) (Fin m) K → Matrix (Fin m) (Fin m) K), Continuous q → (∀ (c : K) w, q (c • w) = (c * star c) • q w) → (∀ w ∈ S, q w = 0 → w = 0) → ∀ Q : Set (Matrix (Fin m) (Fin m) K), IsCompact Q → ∃ B : Set (Matrix (Fin m) (Fin m) K), IsCompact B ∧ ∀ w ∈ S, q w ∈ Q → w ∈ B := by sorry
