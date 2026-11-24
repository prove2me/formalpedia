-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_mid_zero
-- name    : GlobalTheory.CompanionTheory.InertHeis.rad_mid_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:58.335728+00:00
-- url     : https://prove2.me/theorems/fdcefc06-24ee-407f-a099-bb6eea8b1bf0
-- title:
--   Inert Heis: rad mid zero
-- statement:
--   The Inert Heis construction uses the rad mid zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L23-L24

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

theorem GlobalTheory.CompanionTheory.InertHeis.rad_mid_zero (hu : u ∈ radQ σ N) (i : Fin N) : mat u (mid i) 0 = 0 := by sorry
