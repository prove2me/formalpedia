-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_excess_iff
-- name    : GlobalTheory.CompanionTheory.InertLen.excess_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:02:32.543124+00:00
-- url     : https://prove2.me/theorems/dc479982-69a3-4f84-87b1-380ef2bfb10d
-- title:
--   Inert Len: excess iff
-- statement:
--   The Inert Len construction uses the excess iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/PointwiseOfSpanHeisenberg.lean#L93-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/PointwiseOfSpanHeisenberg.lean#L93-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_PointwiseOfSpanHeisenberg
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLen
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.CompanionTheory.InertLen.excess_iff {ι : Type} (R : ι → WithZero (Multiplicative ℤ)) (T : WithZero (Multiplicative ℤ)) (A Y e j : ℕ)
    (hAY : A ≤ Y) (hY : ∀ i, R i ≤ WithZero.exp (Y : ℤ)) (hYs : Y = A ∨ ∃ i, R i = WithZero.exp (Y : ℤ))
    (he₁ : ∀ i, R i ≤ WithZero.exp ((A + e : ℕ) : ℤ)) (he₂ : T ≤ WithZero.exp ((A + Y + e : ℕ) : ℤ))
    (he₃ : e = 0 ∨ (∃ i, R i = WithZero.exp ((A + e : ℕ) : ℤ)) ∨ T = WithZero.exp ((A + Y + e : ℕ) : ℤ)) :
    Y + e ≤ A + j ↔ (∀ i, R i ≤ WithZero.exp ((A + j / 2 : ℕ) : ℤ)) ∧ T ≤ WithZero.exp ((2 * A + j : ℕ) : ℤ) := by sorry
