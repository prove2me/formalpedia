-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_isInt_diagonal
-- name    : GlobalTheory.CompanionTheory.InertZeta.isInt_diagonal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:23:53.81163+00:00
-- url     : https://prove2.me/theorems/3f056e8e-4329-481b-8341-ac772812f3dc
-- title:
--   Inert Zeta: is Int diagonal
-- statement:
--   The Inert Zeta construction uses the is Int diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/FractionExistsOfSmith.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/FractionExistsOfSmith.lean#L12-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_FractionExistsOfSmith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
open GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem GlobalTheory.CompanionTheory.InertZeta.isInt_diagonal {f : Fin n → L} (hf : ∀ i, f i ∈ Formalism.UG.intL L) : IsInt (Matrix.diagonal f) := by sorry
