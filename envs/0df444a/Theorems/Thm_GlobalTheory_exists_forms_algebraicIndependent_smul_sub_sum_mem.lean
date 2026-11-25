-- Prove2me | Theorems.Thm_GlobalTheory_exists_forms_algebraicIndependent_smul_sub_sum_mem
-- name    : GlobalTheory.exists_forms_algebraicIndependent_smul_sub_sum_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:38.797536+00:00
-- url     : https://prove2.me/theorems/4a63b443-e816-4283-822d-5125a2396dc5
-- title:
--   Global Theory: exists forms algebraic Independent smul sub sum mem
-- statement:
--   The Global Theory construction uses the exists forms algebraic Independent smul sub sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L257-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L257-L290

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
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
variable {σ : Type*} {o : Type*} [CommRing o]
variable [Finite σ] [IsDedekindDomain o]

theorem GlobalTheory.exists_forms_algebraicIndependent_smul_sub_sum_mem (I : Ideal (MvPolynomial σ o))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ o))
    [Module.IsTorsionFree o (MvPolynomial σ o ⧸ I)] (lam : Ideal o) [lam.IsMaximal]
    (hlam : lam.map (algebraMap o (MvPolynomial σ o ⧸ I)) ≠ ⊤) :
    ∃ (δ e d₀ : ℕ) (a : o) (F : Fin δ → MvPolynomial σ o),
      ringKrullDim ((MvPolynomial σ o ⧸ I) ⧸ lam.map (algebraMap o (MvPolynomial σ o ⧸ I))) = δ ∧
      a - 1 ∈ lam ∧ 1 ≤ e ∧ e ≤ d₀ ∧ (∀ i, (F i).IsHomogeneous e) ∧
      AlgebraicIndependent o (fun i => Ideal.Quotient.mk I (F i)) ∧
      ∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ o, p.IsHomogeneous d →
        ∃ G : Fin δ → MvPolynomial σ o,
          (∀ i, (G i).IsHomogeneous (d - e)) ∧ a • p - ∑ i, F i * G i ∈ I := by sorry
