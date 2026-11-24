-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentInvariant_exists_cleared
-- name    : GlobalTheory.UnipotentInvariant.exists_cleared
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:25:41.65375+00:00
-- url     : https://prove2.me/theorems/d012cfae-a2d1-4875-a236-48baebfc6f27
-- title:
--   Unipotent Invariant: exists cleared
-- statement:
--   The Unipotent Invariant construction uses the exists cleared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L102-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L102-L171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}

theorem GlobalTheory.UnipotentInvariant.exists_cleared (M : Matrix (Fin p) (Fin p) K) (hM : ∀ i, leadMinor i M ≠ 0) (n : ℕ) :
    ∃ M' : Matrix (Fin p) (Fin p) K, (∀ f, BiInvariant f → f M' = f M) ∧
      ∀ i j : Fin p, i ≠ j → (i.val < n ∨ j.val < n) → M' i j = 0 := by sorry
