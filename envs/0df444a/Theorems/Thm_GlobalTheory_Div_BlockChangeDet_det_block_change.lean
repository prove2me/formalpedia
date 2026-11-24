-- Prove2me | Theorems.Thm_GlobalTheory_Div_BlockChangeDet_det_block_change
-- name    : GlobalTheory.Div.BlockChangeDet.det_block_change
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:50:42.292252+00:00
-- url     : https://prove2.me/theorems/458322af-7996-4162-9c8b-adc4c2990cde
-- title:
--   Block Change Det: det block change
-- statement:
--   The Block Change Det construction uses the det block change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetBlockChangeOfBasisViaTwoFamiliesImplicit.lean#L34-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetBlockChangeOfBasisViaTwoFamiliesImplicit.lean#L34-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetBlockChangeOfBasisViaTwoFamiliesImplicit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.BlockChangeDet
open Matrix

theorem GlobalTheory.Div.BlockChangeDet.det_block_change (F : Type) [Field F] {N : Type} [AddCommGroup N] [Module F N]
    {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N)
    (hℓ : ∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F)
    (hU : ∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) (hA : ∀ k, mu k = ∑ l, A k l • nu l)
    (hg : ∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) :
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by sorry
