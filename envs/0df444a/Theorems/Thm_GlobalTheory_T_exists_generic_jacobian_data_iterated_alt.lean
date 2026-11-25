-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_generic_jacobian_data_iterated_alt
-- name    : GlobalTheory.T.exists_generic_jacobian_data_iterated_alt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:32.916391+00:00
-- url     : https://prove2.me/theorems/bf690e1a-8b6f-5610-b651-3bed169deafc
-- title:
--   T: exists generic jacobian data iterated alt
-- statement:
--   The T construction uses the exists generic jacobian data iterated alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGenericJacobianDataIteratedStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGenericJacobianDataIteratedStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGenericJacobianDataIterated
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGenericJacobianDataIteratedStatement
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

theorem GlobalTheory.T.exists_generic_jacobian_data_iterated_alt : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ τ : Type) [Finite σ] [Finite τ] (Q : Ideal (MvPolynomial τ (MvPolynomial σ Λ))) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0) → ∀ d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ)) (MvPolynomial τ (MvPolynomial σ Λ)), (∀ t x, d (Sum.inl t) x = MvPolynomial.pderiv t x) → (∀ s x, d (Sum.inr s) (MvPolynomial.C x) = MvPolynomial.C (MvPolynomial.pderiv s x)) → (∀ s t, d (Sum.inr s) (MvPolynomial.X t) = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial τ (MvPolynomial σ Λ)) (s : Fin h → τ ⊕ σ) (g : MvPolynomial τ (MvPolynomial σ Λ)), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => d (s i) (f j)).det ∉ Q := by sorry
