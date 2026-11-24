-- Prove2me | Theorems.Thm_GlobalTheory_quadratic_preimage_compact_on_subspace
-- name    : GlobalTheory.quadratic_preimage_compact_on_subspace
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:15:08.795801+00:00
-- url     : https://prove2.me/theorems/06915bf3-7393-4c31-9185-a36c48556dcf
-- title:
--   Global Theory: quadratic preimage compact on subspace
-- statement:
--   The Global Theory construction uses the quadratic preimage compact on subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCompactPreimageQuadraticMapNoNullVectors.lean#L8-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCompactPreimageQuadraticMapNoNullVectors.lean#L8-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactPreimageQuadraticMapNoNullVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem GlobalTheory.quadratic_preimage_compact_on_subspace
    (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K]
    (hstar : ∀ x : K, ‖star x‖ = ‖x‖) (m : ℕ) (S : Submodule K (Matrix (Fin m) (Fin m) K))
    (q : Matrix (Fin m) (Fin m) K → Matrix (Fin m) (Fin m) K) (hq : Continuous q)
    (hhom : ∀ (c : K) w, q (c • w) = (c * star c) • q w) (hnull : ∀ w ∈ S, q w = 0 → w = 0)
    (Q : Set (Matrix (Fin m) (Fin m) K)) (hQ : IsCompact Q) :
    ∃ B : Set (Matrix (Fin m) (Fin m) K), IsCompact B ∧ ∀ w ∈ S, q w ∈ Q → w ∈ B := by sorry
