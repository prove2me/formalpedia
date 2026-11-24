-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_zero_zero
-- name    : GlobalTheory.CompanionTheory.InertHeis.rad_zero_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:48:41.86426+00:00
-- url     : https://prove2.me/theorems/5b16c0c6-d66a-4a01-aca9-a5e4e5347fce
-- title:
--   Inert Heis: rad zero zero
-- statement:
--   The Inert Heis construction uses the rad zero zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L20-L21

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
variable {u : GU σ (N + 2)}

theorem GlobalTheory.CompanionTheory.InertHeis.rad_zero_zero (hu : u ∈ radQ σ N) : mat u 0 0 = 1 := by sorry
