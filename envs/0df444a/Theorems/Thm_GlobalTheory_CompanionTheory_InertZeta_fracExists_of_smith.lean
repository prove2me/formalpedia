-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_fracExists_of_smith
-- name    : GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:23:21.726374+00:00
-- url     : https://prove2.me/theorems/ba5eeeb4-2f01-4dda-9997-b797340dc404
-- title:
--   Inert Zeta: frac Exists of smith
-- statement:
--   The Inert Zeta construction uses the frac Exists of smith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/FractionExistsOfSmith.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/FractionExistsOfSmith.lean#L64-L69

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

theorem GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith : Smith → FracExists := by sorry
