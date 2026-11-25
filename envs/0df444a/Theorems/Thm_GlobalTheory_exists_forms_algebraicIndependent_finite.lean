-- Prove2me | Theorems.Thm_GlobalTheory_exists_forms_algebraicIndependent_finite
-- name    : GlobalTheory.exists_forms_algebraicIndependent_finite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:23.035783+00:00
-- url     : https://prove2.me/theorems/0ac2a4e7-2e86-4fa0-92a4-f61b719e3015
-- title:
--   Global Theory: exists forms algebraic Independent finite
-- statement:
--   The Global Theory construction uses the exists forms algebraic Independent finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L320-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L320-L350

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
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
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ : Type*} [Finite σ] {k : Type*} [Field k]

theorem GlobalTheory.exists_forms_algebraicIndependent_finite {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) {δ : ℕ}
    (hdim : ringKrullDim (MvPolynomial σ k ⧸ I) = δ) :
    ∃ (e d₀ : ℕ) (F : Fin δ → MvPolynomial σ k), 1 ≤ e ∧ e ≤ d₀ ∧
      (∀ i, (F i).IsHomogeneous e) ∧
      AlgebraicIndependent k (fun i => Ideal.Quotient.mk I (F i)) ∧
      (∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ k, p.IsHomogeneous d →
        ∃ G : Fin δ → MvPolynomial σ k,
          (∀ i, (G i).IsHomogeneous (d - e)) ∧ p - ∑ i, F i * G i ∈ I) ∧
      (aeval (fun i => Ideal.Quotient.mk I (F i)) :
        MvPolynomial (Fin δ) k →ₐ[k] MvPolynomial σ k ⧸ I).Finite := by sorry
