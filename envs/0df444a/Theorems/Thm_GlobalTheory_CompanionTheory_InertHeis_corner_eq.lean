-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_corner_eq
-- name    : GlobalTheory.CompanionTheory.InertHeis.corner_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:07.046948+00:00
-- url     : https://prove2.me/theorems/79ef167c-4448-4c5b-a243-54075603471b
-- title:
--   Inert Heis: corner eq
-- statement:
--   The Inert Heis construction uses the corner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L161-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L161-L165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertHeis.corner_eq {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) :
    cornerOf u + σ (cornerOf u) = rowOf u ⬝ᵥ colOf u := by sorry
