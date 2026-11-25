-- Prove2me | Theorems.Thm_GlobalTheory_T_block_basis_change_entries
-- name    : GlobalTheory.T.block_basis_change_entries
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:05.043897+00:00
-- url     : https://prove2.me/theorems/de321220-5d75-45f3-adec-5ad558624dd1
-- title:
--   T: block basis change entries
-- statement:
--   The T construction uses the block basis change entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/AdaptedFrameOrthogonalSubspaceStatement.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/AdaptedFrameOrthogonalSubspaceStatement.lean#L7-L13

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_AdaptedFrameOrthogonalSubspace
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_AdaptedFrameOrthogonalSubspaceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.block_basis_change_entries : ∀ (n n' a : ℕ) (hdim : a + n' + a = n) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P.det →
    ∀ (J : Matrix (Fin n) (Fin n') ℂ) (Jp : Matrix (Fin n') (Fin n) ℂ) (B Bi : Matrix (Fin n') (Fin n') ℂ), Jp * J = 1 → B * Bi = 1 →
    (∀ (i : Fin n) (j : Fin n'), J i j = ∑ r : Fin n', P i (⟨a + r.val, by omega⟩ : Fin n) * B r j) →
    (∀ b : Fin n, (b.val < a ∨ n ≤ b.val + a) → Jp *ᵥ (fun k => P k b) = 0) →
    ∀ p q : Fin n', J * Matrix.single p q (1 : ℂ) * Jp = ∑ r : Fin n', ∑ u : Fin n', (B r p * Bi q u) •
      (P * Matrix.single (⟨a + r.val, by omega⟩ : Fin n) (⟨a + u.val, by omega⟩ : Fin n) (1 : ℂ) * P⁻¹) := by sorry
