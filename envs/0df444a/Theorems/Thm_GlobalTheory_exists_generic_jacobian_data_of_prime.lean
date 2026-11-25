-- Prove2me | Theorems.Thm_GlobalTheory_exists_generic_jacobian_data_of_prime
-- name    : GlobalTheory.exists_generic_jacobian_data_of_prime
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:28.740286+00:00
-- url     : https://prove2.me/theorems/17bc9217-7283-4b31-9d6e-adc7796297fa
-- title:
--   Global Theory: exists generic jacobian data of prime
-- statement:
--   The Global Theory construction uses the exists generic jacobian data of prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGenericJacobianDataOfPrime.lean#L9-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGenericJacobianDataOfPrime.lean#L9-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSqLocalizationOfPderivMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDetNeZeroOfRowsSeparatingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMinimalLocalGeneratorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGenericJacobianDataOfPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_generic_jacobian_data_of_prime (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ]
    (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime] (hQ : ∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) :
    ∃ (h : ℕ) (f : Fin h → MvPolynomial σ Λ) (s : Fin h → σ) (g : MvPolynomial σ Λ),
      g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
      (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det ∉ Q := by sorry
