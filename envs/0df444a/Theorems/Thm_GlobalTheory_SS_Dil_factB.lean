-- Prove2me | Theorems.Thm_GlobalTheory_SS_Dil_factB
-- name    : GlobalTheory.SS.Dil.factB
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:34:07.688807+00:00
-- url     : https://prove2.me/theorems/a4ee9c7b-34c5-437a-849f-818616dd4e59
-- title:
--   Dil: fact B
-- statement:
--   The Dil construction uses the fact B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L214-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L214-L255

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

theorem GlobalTheory.SS.Dil.factB {R B S : Type} {n : ℕ} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
    (q : MvPolynomial (Fin n) R →ₐ[R] B) (hq : Function.Surjective q) (σ : MvPolynomial (Fin n) R →+* S)
    (hσ : ∀ p, σ p = algebraMap B S (q p)) (hs : Function.Surjective σ)
    [Module.Projective S (S ⊗[B] KaehlerDifferential R B)] :
    ∃ h : Fin n → MvPolynomial (Fin n) R, (∀ j, q (h j) = 0) ∧
      ∀ f, q f = 0 → gr σ (f - ∑ j, pderiv j f * h j) = 0 := by sorry
