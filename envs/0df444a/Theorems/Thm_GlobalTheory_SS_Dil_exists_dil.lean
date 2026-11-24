-- Prove2me | Theorems.Thm_GlobalTheory_SS_Dil_exists_dil
-- name    : GlobalTheory.SS.Dil.exists_dil
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:33:47.954734+00:00
-- url     : https://prove2.me/theorems/645574c8-467a-417e-918f-f6e0ac74ad9c
-- title:
--   Dil: exists dil
-- statement:
--   The Dil construction uses the exists dil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L496-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L496-L509

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

theorem GlobalTheory.SS.Dil.exists_dil (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (hπ : Irreducible π)
    (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B] (I : Ideal B) :
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (φ : B →ₐ[R] B'), Algebra.FiniteType R B' ∧ Module.Flat R B' ∧
      Function.Injective φ ∧ (∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) ∧
      (∀ x, algebraMap R B' π * x = 0 → x = 0) ∧ (∀ g ∈ I, ∃ b', algebraMap R B' π * b' = φ g) ∧
      (∀ Q : B' → Prop, (∀ b, Q (φ b)) → (∀ g ∈ I, ∀ b', algebraMap R B' π * b' = φ g → Q b') →
        (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x) := by sorry
