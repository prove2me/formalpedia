-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_levi_step
-- name    : GlobalTheory.CompanionTheory.InertCoset.levi_step
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:02:59.108675+00:00
-- url     : https://prove2.me/theorems/0a18d5a1-5d44-4256-ae81-2bb66270c38d
-- title:
--   Inert Coset: levi step
-- statement:
--   The Inert Coset construction uses the levi step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L571-L709
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L571-L709

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

theorem GlobalTheory.CompanionTheory.InertCoset.levi_step (hLE : LeviExists) {ϖ : L} {q N : ℕ} (hU : IsUnramInv ϖ σ q) {s : ℤ} (p : GU σ (N + 2))
    (hp : ∀ i, mat p i 0 = ϖ ^ s * (Pi.single 0 1 : Fin (N + 2) → L) i) :
    ∃ y : GU σ N ⧸ KU σ N, ∀ m, IsLeviElt ϖ s y.out m →
      ∃ u ∈ radQ σ N, ∃ k ∈ KU σ (N + 2), p = m * u * k := by sorry
