-- Prove2me | Theorems.Thm_GlobalTheory_exists_basis_adapted_to_cartan_involution
-- name    : GlobalTheory.exists_basis_adapted_to_cartan_involution
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:19.546556+00:00
-- url     : https://prove2.me/theorems/6a3aa998-5b0a-4e04-9550-ff4fd8bc20fe
-- title:
--   Global Theory: exists basis adapted to cartan involution
-- statement:
--   The Global Theory construction uses the exists basis adapted to cartan involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasisAdaptedToCartanInvolution.lean#L72-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasisAdaptedToCartanInvolution.lean#L72-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisAdaptedToCartanInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory

theorem GlobalTheory.exists_basis_adapted_to_cartan_involution :
    ∀ (n : ℕ) (G s : Matrix (Fin n) (Fin n) ℂ), s * s = 1 → sᴴ * G * s = G → (G * s).PosDef →
      ∃ (p q : ℕ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
        (B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), B * B' = 1 ∧ B' * B = 1 ∧
        Bᴴ * G * B = Matrix.fromBlocks 1 0 0 (-1) ∧
        s * B = B * Matrix.fromBlocks 1 0 0 (-1) := by sorry
