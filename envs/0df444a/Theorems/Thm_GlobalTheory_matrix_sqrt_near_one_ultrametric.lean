-- Prove2me | Theorems.Thm_GlobalTheory_matrix_sqrt_near_one_ultrametric
-- name    : GlobalTheory.matrix_sqrt_near_one_ultrametric
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:11:25.572384+00:00
-- url     : https://prove2.me/theorems/40db5612-9ce9-41b9-bc71-50938d36ec8a
-- title:
--   Global Theory: matrix sqrt near one ultrametric
-- statement:
--   The Global Theory construction uses the matrix sqrt near one ultrametric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L139-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L139-L153

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
open GlobalTheory

theorem GlobalTheory.matrix_sqrt_near_one_ultrametric :
    ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] (n : ℕ) (σ : K →+* K), Continuous σ →
      ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) K), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) K,
        r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K, a * s = s * a → a * r = r * a) ∧
        ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by sorry
