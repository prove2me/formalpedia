-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_exists_K_unit
-- name    : GlobalTheory.CompanionTheory.InertCoset.exists_K_unit
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:01:27.344833+00:00
-- url     : https://prove2.me/theorems/a131b368-134b-47e1-9990-9943340529a0
-- title:
--   Inert Coset: exists K unit
-- statement:
--   The Inert Coset construction uses the exists K unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L260-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L260-L349

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

theorem GlobalTheory.CompanionTheory.InertCoset.exists_K_unit {N : ℕ} (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {z : L}
    (hz : Valued.v z = 1) :
    ∃ k ∈ KU σ (N + 2), mat k *ᵥ (Pi.single 0 1 : Fin (N + 2) → L) = z • Pi.single 0 1 := by sorry
