-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_exists_K_of_pair
-- name    : GlobalTheory.CompanionTheory.InertCoset.exists_K_of_pair
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:54:20.613281+00:00
-- url     : https://prove2.me/theorems/558fb6f6-f18a-4c24-8030-2affe0b06db8
-- title:
--   Inert Coset: exists K of pair
-- statement:
--   The Inert Coset construction uses the exists K of pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L160-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L160-L201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem GlobalTheory.CompanionTheory.InertCoset.exists_K_of_pair (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {e w : Fin n → L}
    (he : ∀ i, e i ∈ intL L) (hw : ∀ i, w i ∈ intL L) (hee : hf σ e e = 0) (hww : hf σ w w = 0)
    (hew : hf σ e w = 1) : ∃ k ∈ KU σ n, mat k *ᵥ e = w := by sorry
