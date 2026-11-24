-- Prove2me | Theorems.Thm_GlobalTheory_SS_Dil_core
-- name    : GlobalTheory.SS.Dil.core
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:34:07.322445+00:00
-- url     : https://prove2.me/theorems/9e4f9a4f-8c84-496d-96ae-7f9cab7af747
-- title:
--   Dil: core
-- statement:
--   The Dil construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L257-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L257-L438

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil

theorem GlobalTheory.SS.Dil.core {R B B' S : Type} {n : ℕ} [CommRing R] [CommRing B] [CommRing B'] [CommRing S] [Algebra R B] [Algebra R B']
    [Algebra B S] [Algebra B' S] (q : MvPolynomial (Fin n) R →ₐ[R] B) (hq : Function.Surjective q)
    (σ : MvPolynomial (Fin n) R →+* S) (hσ : ∀ p, σ p = algebraMap B S (q p))
    (φ : B →ₐ[R] B') (hφ : ∀ b, algebraMap B' S (φ b) = algebraMap B S b) (π : R) (ϖ : S)
    (hϖ : algebraMap B' S (algebraMap R B' π) = ϖ) (hreg : ∀ x, ϖ * x = 0 → x = 0)
    (hreg' : ∀ x, algebraMap R B' π * x = 0 → x = 0) (I : Ideal (MvPolynomial (Fin n) R))
    (hβ : ∀ g ∈ I, ∃ b', algebraMap R B' π * b' = φ (q g)) (hJ : ∀ f, q f = 0 → f ∈ I)
    (hgen : ∀ Q : B' → Prop, (∀ b, Q (φ b)) → (∀ g ∈ I, ∀ b', algebraMap R B' π * b' = φ (q g) → Q b') →
      (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x)
    (h : Fin n → MvPolynomial (Fin n) R) (hh : ∀ j, h j ∈ I)
    (hA : ∀ g ∈ I, ∃ p, g - ∑ j, pderiv j g * h j - MvPolynomial.C π * p ∈ I * I)
    (h' : Fin n → MvPolynomial (Fin n) R) (hh' : ∀ j, q (h' j) = 0)
    (hB : ∀ f, q f = 0 → f - ∑ j, pderiv j f * h' j ∈ I * I)
    (m : S ⊗[B'] KaehlerDifferential R B') :
    ∃ u : Fin n → S, ϖ • m = ∑ i, u i • dd R B' S (φ (q (X i))) ∧
      ∀ c : ℕ, ϖ ^ (c + 1) • ∑ i, u i • dd R B S (q (X i)) = 0 → ϖ ^ c • m = 0 := by sorry
