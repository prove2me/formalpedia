-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_exp_inv_mul_eq
-- name    : GlobalTheory.CompanionTheory.InertLen.exp_inv_mul_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:02:43.997104+00:00
-- url     : https://prove2.me/theorems/f0a3de2b-b3ec-4981-980a-6fac467e521e
-- title:
--   Inert Len: exp inv mul eq
-- statement:
--   The Inert Len construction uses the exp inv mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/PointwiseOfSpanHeisenberg.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/PointwiseOfSpanHeisenberg.lean#L23-L33

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

theorem GlobalTheory.CompanionTheory.InertLen.exp_inv_mul_eq (n e : ℕ) (x : WithZero (Multiplicative ℤ)) :
    (WithZero.exp (n : ℤ))⁻¹ * x = WithZero.exp (e : ℤ) ↔ x = WithZero.exp ((n + e : ℕ) : ℤ) := by sorry
