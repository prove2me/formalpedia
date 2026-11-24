-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_reversedCharpolyCoeff_not_mem_prime
-- name    : GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:38:33.518719+00:00
-- url     : https://prove2.me/theorems/d3d714db-b213-49c5-8a7e-864b082c89c0
-- title:
--   T: exists reversed Charpoly Coeff not mem prime
-- statement:
--   The T construction uses the exists reversed Charpoly Coeff not mem prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsReversedCharpolyCoeffNotMemPrimeStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsReversedCharpolyCoeffNotMemPrimeStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsReversedCharpolyCoeffNotMemPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsReversedCharpolyCoeffNotMemPrimeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (b : B), (∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = ⊥) → ∀ p : Ideal A, p.IsPrime →
    (∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∉ Q) → ∃ k, 1 ≤ k ∧ normCoeff φ hφ b k ∉ p := by sorry
