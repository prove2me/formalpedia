-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_cornerOf_inv
-- name    : GlobalTheory.CompanionTheory.InertHeis.cornerOf_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:48:44.256348+00:00
-- url     : https://prove2.me/theorems/4a458fac-ee3c-4cee-b8f5-1b27a60ddad6
-- title:
--   Inert Heis: corner Of inv
-- statement:
--   The Inert Heis construction uses the corner Of inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L145-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean#L145-L147

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

theorem GlobalTheory.CompanionTheory.InertHeis.cornerOf_inv (u : GU σ (N + 2)) : cornerOf u⁻¹ = σ (cornerOf u) := by sorry
