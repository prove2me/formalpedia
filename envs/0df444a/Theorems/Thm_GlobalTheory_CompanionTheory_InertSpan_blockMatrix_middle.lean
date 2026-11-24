-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_middle
-- name    : GlobalTheory.CompanionTheory.InertSpan.blockMatrix_middle
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:51:32.447864+00:00
-- url     : https://prove2.me/theorems/887e94a6-2133-4305-95be-33be2c2f5c2e
-- title:
--   Inert Span: block Matrix middle
-- statement:
--   The Inert Span construction uses the block Matrix middle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L53-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertSpan
variable {L : Type} [Field L] {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertSpan.blockMatrix_middle (p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) (j : Fin N) :
    mat3 p M l (mid j) = M j := by sorry
