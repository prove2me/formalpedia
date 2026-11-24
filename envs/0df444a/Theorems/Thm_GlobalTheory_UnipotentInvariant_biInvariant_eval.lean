-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentInvariant_biInvariant_eval
-- name    : GlobalTheory.UnipotentInvariant.biInvariant_eval
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:25:23.656308+00:00
-- url     : https://prove2.me/theorems/27909ae3-e616-43cf-b517-64b0c3ddd277
-- title:
--   Unipotent Invariant: bi Invariant eval
-- statement:
--   The Unipotent Invariant construction uses the bi Invariant eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L246-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L246-L278

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
variable {σ : Type*} [DecidableEq σ]

theorem GlobalTheory.UnipotentInvariant.biInvariant_eval {z : Fin p × Fin p → σ} (hz : Function.Injective z)
    (P : MvPolynomial σ K)
    (hr : ∀ a b : Fin p, a < b → ∀ t : K,
      bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (hc : ∀ k l : Fin p, k < l → ∀ t : K,
      bind₁ (fun s => X s + ∑ a, if s = z (a, l) then C t * X (z (a, k)) else 0) P = P)
    (x : σ → K) : BiInvariant fun M => eval (setBlock z x M) P := by sorry
