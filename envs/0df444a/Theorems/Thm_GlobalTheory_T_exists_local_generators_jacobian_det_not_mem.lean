-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_local_generators_jacobian_det_not_mem
-- name    : GlobalTheory.T.exists_local_generators_jacobian_det_not_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:01.976279+00:00
-- url     : https://prove2.me/theorems/b6e4c34b-967d-4b76-82fc-9be8c8f5746a
-- title:
--   T: exists local generators jacobian det not mem
-- statement:
--   The T construction uses the exists local generators jacobian det not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGenericJacobianDataOfPrimeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGenericJacobianDataOfPrimeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGenericJacobianDataOfPrime
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGenericJacobianDataOfPrimeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_local_generators_jacobian_det_not_mem : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial σ Λ) (s : Fin h → σ) (g : MvPolynomial σ Λ), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det ∉ Q := by sorry
