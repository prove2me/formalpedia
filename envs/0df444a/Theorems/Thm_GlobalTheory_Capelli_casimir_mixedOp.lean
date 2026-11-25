-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_casimir_mixedOp
-- name    : GlobalTheory.Capelli.casimir_mixedOp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:23.656402+00:00
-- url     : https://prove2.me/theorems/fca2bce1-49a7-4d4d-b9eb-f11ca3835e52
-- title:
--   Capelli: casimir mixed Op
-- statement:
--   The Capelli construction uses the casimir mixed Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L260-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L260-L278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open Capelli
open GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K] {p q n : ℕ}

theorem GlobalTheory.Capelli.casimir_mixedOp (z : Fin p × Fin n → σ) (hz : Function.Injective z)
    (y : Fin q × Fin n → σ) (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w)
    (P : MvPolynomial σ K) :
    ∑ k, ∑ l, mixedOp K z y k l (mixedOp K z y l k P) =
      (∑ a, ∑ b, rowOp K z a b (rowOp K z b a P) +
        ((n : K) - (p : K)) • ∑ a, rowOp K z a a P) +
      (∑ a, ∑ b, rowOp K y a b (rowOp K y b a P) +
        ((n : K) - (q : K)) • ∑ a, rowOp K y a a P) -
      (2 : K) • ∑ a, ∑ b, (∑ k, X (z (a, k)) * X (y (b, k))) *
        ∑ l, pderiv (z (a, l)) (pderiv (y (b, l)) P) := by sorry
