-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_isotropic_graph_det_ne_zero
-- name    : GlobalTheory.T.exists_isotropic_graph_det_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:36:57.377468+00:00
-- url     : https://prove2.me/theorems/5f19dded-ee29-4a0c-9fcc-9ce0ca3ec338
-- title:
--   T: exists isotropic graph det ne zero
-- statement:
--   The T construction uses the exists isotropic graph det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsotropicGraphDetLowerRowNeZeroFieldStatement.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsotropicGraphDetLowerRowNeZeroFieldStatement.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsotropicGraphDetLowerRowNeZeroField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsotropicGraphDetLowerRowNeZeroFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_isotropic_graph_det_ne_zero : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧ (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by sorry
