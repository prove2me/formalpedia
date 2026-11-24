-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentInvariant_BiInvariant_eq_mul_prod
-- name    : GlobalTheory.UnipotentInvariant.BiInvariant.eq_mul_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:25:27.956856+00:00
-- url     : https://prove2.me/theorems/d08e81ae-60bc-4295-aa41-832554b5ce19
-- title:
--   Bi Invariant: eq mul prod
-- statement:
--   The Bi Invariant construction uses the eq mul prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L213-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L213-L220

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

theorem GlobalTheory.UnipotentInvariant.BiInvariant.eq_mul_prod {f : Matrix (Fin p) (Fin p) K → K} (hf : BiInvariant f)
    (c : Fin p → ℕ)
    (hd : ∀ d, f (diagonal d) = f 1 * ∏ a, d a ^ ∑ i ∈ Finset.Ici a, c i)
    (M : Matrix (Fin p) (Fin p) K) (hM : ∀ i, leadMinor i M ≠ 0) :
    f M = f 1 * ∏ i, leadMinor i M ^ c i := by sorry
