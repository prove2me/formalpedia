-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_vec_ext
-- name    : GlobalTheory.CompanionTheory.InertSpan.vec_ext
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:51:46.158209+00:00
-- url     : https://prove2.me/theorems/49f04580-ddb6-4c43-bebf-dbaf043a00ca
-- title:
--   Inert Span: vec ext
-- statement:
--   The Inert Span construction uses the vec ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L25-L31

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

theorem GlobalTheory.CompanionTheory.InertSpan.vec_ext {f h : Fin (N + 2) → L} (h0 : f 0 = h 0) (hm : ∀ j, f (mid j) = h (mid j))
    (hl : f (Fin.last (N + 1)) = h (Fin.last (N + 1))) : f = h := by sorry
