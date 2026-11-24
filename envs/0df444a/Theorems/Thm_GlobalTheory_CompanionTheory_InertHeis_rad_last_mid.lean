-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_last_mid
-- name    : GlobalTheory.CompanionTheory.InertHeis.rad_last_mid
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:23:19.959906+00:00
-- url     : https://prove2.me/theorems/ecbbf780-b2c5-4597-a092-16d6d8c5b705
-- title:
--   Inert Heis: rad last mid
-- statement:
--   The Inert Heis construction uses the rad last mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L34-L35

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

theorem GlobalTheory.CompanionTheory.InertHeis.rad_last_mid (hu : u ∈ radQ σ N) (j : Fin N) : mat u (Fin.last (N + 1)) (mid j) = 0 := by sorry
