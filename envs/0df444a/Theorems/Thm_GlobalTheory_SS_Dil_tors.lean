-- Prove2me | Theorems.Thm_GlobalTheory_SS_Dil_tors
-- name    : GlobalTheory.SS.Dil.tors
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:33:19.344818+00:00
-- url     : https://prove2.me/theorems/d1a021bb-672d-417b-ac5c-8660510a9d1a
-- title:
--   Dil: tors
-- statement:
--   The Dil construction uses the tors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L440-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L440-L494

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

theorem GlobalTheory.SS.Dil.tors {R B B' S : Type} [CommRing R] [CommRing B] [CommRing B'] [CommRing S] [Algebra R B] [Algebra R B']
    [Algebra B S] [Algebra B' S] (φ : B →ₐ[R] B') (hφ : ∀ b, algebraMap B' S (φ b) = algebraMap B S b) (π : R) (ϖ : S)
    (hϖ : algebraMap B' S (algebraMap R B' π) = ϖ) (hreg : ϖ ∈ nonZeroDivisors S) (hinj : Function.Injective φ)
    (hden : ∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) {n : ℕ} (u : Fin n → S) (x : Fin n → B)
    (hu : ∑ i, u i • dd R B' S (φ (x i)) ∈ Submodule.torsion S (S ⊗[B'] KaehlerDifferential R B')) :
    ∑ i, u i • dd R B S (x i) ∈ Submodule.torsion S (S ⊗[B] KaehlerDifferential R B) := by sorry
