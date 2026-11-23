-- Prove2me | Theorems.Thm_GlobalTheory_finite_aeval_of_forms_eq_sum
-- name    : GlobalTheory.finite_aeval_of_forms_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:59.501187+00:00
-- url     : https://prove2.me/theorems/cb737a2c-30ec-4712-aae8-b39fc9eb74db
-- title:
--   Global Theory: finite aeval of forms eq sum
-- statement:
--   The Global Theory construction uses the finite aeval of forms eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L239-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L239-L277

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
variable {σ ι R S : Type*} [CommRing R] [Fintype ι] [CommRing S] [Algebra R S]

theorem GlobalTheory.finite_aeval_of_forms_eq_sum [Finite σ] (π : MvPolynomial σ R →ₐ[R] S)
    (hπ : Function.Surjective π) (f : ι → S) {e d₀ : ℕ} (he : 0 < e) (hed : e ≤ d₀)
    (h : ∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ R, p.IsHomogeneous d →
      ∃ G : ι → MvPolynomial σ R,
        (∀ i, (G i).IsHomogeneous (d - e)) ∧ π p = ∑ i, f i * π (G i)) :
    (aeval f : MvPolynomial ι R →ₐ[R] S).Finite := by sorry
