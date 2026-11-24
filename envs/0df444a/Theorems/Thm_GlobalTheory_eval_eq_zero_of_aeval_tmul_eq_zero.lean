-- Prove2me | Theorems.Thm_GlobalTheory_eval_eq_zero_of_aeval_tmul_eq_zero
-- name    : GlobalTheory.eval_eq_zero_of_aeval_tmul_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:20:03.094627+00:00
-- url     : https://prove2.me/theorems/ecfefe40-1fc8-497a-9f55-a8b5cc9f6c6b
-- title:
--   Global Theory: eval eq zero of aeval tmul eq zero
-- statement:
--   The Global Theory construction uses the eval eq zero of aeval tmul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCompleteDiscreteValuationRingOfMemClosureCones.lean#L29-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCompleteDiscreteValuationRingOfMemClosureCones.lean#L29-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureCones
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators TensorProduct
open GlobalTheory

theorem GlobalTheory.eval_eq_zero_of_aeval_tmul_eq_zero {F K J ι : Type} [Field F] [Field K] [Algebra F K]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)] (w : ∀ i, J → A i) (v : J → K)
    (h : ∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d →
      (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0)
    (G : MvPolynomial J K) (d : ℕ) (hG : G.IsHomogeneous d)
    (h0 : ∀ i, MvPolynomial.aeval (fun j => (1 : K) ⊗ₜ[F] w i j) G = 0) :
    MvPolynomial.eval v G = 0 := by sorry
