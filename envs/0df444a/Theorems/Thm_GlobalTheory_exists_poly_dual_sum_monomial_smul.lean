-- Prove2me | Theorems.Thm_GlobalTheory_exists_poly_dual_sum_monomial_smul
-- name    : GlobalTheory.exists_poly_dual_sum_monomial_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:36:34.802264+00:00
-- url     : https://prove2.me/theorems/8ba57c6b-4e3f-46c9-b587-f4ba7b7cdc4e
-- title:
--   Global Theory: exists poly dual sum monomial smul
-- statement:
--   The Global Theory construction uses the exists poly dual sum monomial smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L69-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L69-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
variable {σ A K V : Type*} [Finite σ] [Field K] [CharZero K] [CommSemiring A] [Algebra A K]
  [AddCommGroup V] [Module K V]
omit [Finite σ] [CharZero K]

theorem GlobalTheory.exists_poly_dual_sum_monomial_smul (d : ℕ) (s : Finset (σ →₀ ℕ)) (v : (σ →₀ ℕ) → V)
    (hs : ∀ a ∈ s, ∀ i, a i ≤ d) (l : Module.Dual K V) :
    ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧ ∀ x : σ → A,
      l (∑ a ∈ s, (a.prod fun i n => algebraMap A K (x i) ^ n) • v a) =
        eval (fun i => algebraMap A K (x i)) P := by sorry
