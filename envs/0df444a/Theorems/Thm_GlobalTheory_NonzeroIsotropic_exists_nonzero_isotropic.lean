-- Prove2me | Theorems.Thm_GlobalTheory_NonzeroIsotropic_exists_nonzero_isotropic
-- name    : GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:02.310613+00:00
-- url     : https://prove2.me/theorems/57101b73-3d04-4f75-aeb9-c705f9551b86
-- title:
--   Nonzero Isotropic: exists nonzero isotropic
-- statement:
--   The Nonzero Isotropic construction uses the exists nonzero isotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNonzeroIsotropic.lean#L20-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNonzeroIsotropic.lean#L20-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNonzeroIsotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.NonzeroIsotropic
open MvPolynomial

theorem GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic :
    ∀ {k : Type u_1} [inst : Field k] [Finite k] (a : Fin (3 : ℕ) → Fin (3 : ℕ) → k),
      ∃ (x : Fin (3 : ℕ) → k), x ≠ (0 : Fin (3 : ℕ) → k) ∧
        ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), a i j * x i * x j = (0 : k) := by sorry
