-- Prove2me | Theorems.Thm_GlobalTheory_linForm_elimination
-- name    : GlobalTheory.linForm_elimination
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:34.205485+00:00
-- url     : https://prove2.me/theorems/1de05b04-b1f5-5cbd-8e4d-216d5a09791e
-- title:
--   Global Theory: lin Form elimination
-- statement:
--   The Global Theory construction uses the lin Form elimination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L458-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L458-L483

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
include hu

theorem GlobalTheory.linForm_elimination (S : Set ι) (σ : Type*) :
    (∃ φ : MvPolynomial (ι × J) R ≃ₐ[R] MvPolynomial (ι × J) R,
      (∀ i ∈ S, φ (X (i, j₀)) = ∑ j, C (u j) * X (i, j)) ∧
      ∀ x : ι × J, ¬ (x.1 ∈ S ∧ x.2 = j₀) → φ (X x) = X x) ∧
    (∃ ψ : (MvPolynomial (ι × J) R ⧸ Ideal.span (linForm u '' S)) ≃ₐ[R]
        MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R,
      ∀ x : {x : ι × J // x ∉ elimIndices S j₀}, ψ (Ideal.Quotient.mk _ (X x.1)) = X x) ∧
    (∀ l : List ι, l.Nodup →
      IsWeaklyRegular (MvPolynomial (ι × J) R) (l.map (linForm u)) ∧
      (Nontrivial R →
        RingTheory.Sequence.IsRegular (MvPolynomial (ι × J) R) (l.map (linForm u))) ∧
      ∀ r ∈ nonZeroDivisors R,
        IsWeaklyRegular (MvPolynomial (ι × J) R) (C r :: l.map (linForm u)) ∧
        (¬ IsUnit r →
          RingTheory.Sequence.IsRegular (MvPolynomial (ι × J) R) (C r :: l.map (linForm u)))) ∧
    (∀ l : List σ, l.Nodup →
      IsWeaklyRegular (MvPolynomial σ R) (l.map X : List (MvPolynomial σ R)) ∧
      (Nontrivial R →
        RingTheory.Sequence.IsRegular (MvPolynomial σ R) (l.map X : List (MvPolynomial σ R)))) := by sorry
