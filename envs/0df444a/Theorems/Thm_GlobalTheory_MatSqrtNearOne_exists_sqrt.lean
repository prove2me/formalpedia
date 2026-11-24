-- Prove2me | Theorems.Thm_GlobalTheory_MatSqrtNearOne_exists_sqrt
-- name    : GlobalTheory.MatSqrtNearOne.exists_sqrt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:40.944104+00:00
-- url     : https://prove2.me/theorems/cb1cec86-cc5b-47e5-b7c2-7e727c7d0a1f
-- title:
--   Mat Sqrt Near One: exists sqrt
-- statement:
--   The Mat Sqrt Near One construction uses the exists sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L88-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L88-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open GlobalTheory GlobalTheory.MatSqrtNearOne
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] {n : ℕ}

theorem GlobalTheory.MatSqrtNearOne.exists_sqrt [CompleteSpace K] [CharZero K] (σ : K →+* K) (hσ : Continuous σ)
    (s : Matrix (Fin n) (Fin n) K)
    (hs : ∀ i j, ‖s i j - (1 : Matrix (Fin n) (Fin n) K) i j‖ < ‖(4 : K)‖) :
    ∃ r : Matrix (Fin n) (Fin n) K, r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K,
      a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by sorry
