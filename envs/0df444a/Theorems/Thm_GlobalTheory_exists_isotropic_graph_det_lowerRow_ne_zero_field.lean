-- Prove2me | Theorems.Thm_GlobalTheory_exists_isotropic_graph_det_lowerRow_ne_zero_field
-- name    : GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:37.020686+00:00
-- url     : https://prove2.me/theorems/b317da16-ee88-439e-af7c-63eb2887883a
-- title:
--   Global Theory: exists isotropic graph det lower Row ne zero field
-- statement:
--   The Global Theory construction uses the exists isotropic graph det lower Row ne zero field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsotropicGraphDetLowerRowNeZeroField.lean#L7-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsotropicGraphDetLowerRowNeZeroField.lean#L7-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSkewHermitianMulAddDetNeZeroOfPairStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsotropicGraphDetLowerRowNeZeroField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory

theorem GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧
        (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by sorry
