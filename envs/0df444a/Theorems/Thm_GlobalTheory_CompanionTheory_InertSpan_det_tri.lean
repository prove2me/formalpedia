-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_det_tri
-- name    : GlobalTheory.CompanionTheory.InertSpan.det_tri
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:03:54.097946+00:00
-- url     : https://prove2.me/theorems/2fbb5045-b780-4d9a-ab9c-6c6738a9bca6
-- title:
--   Inert Span: det tri
-- statement:
--   The Inert Span construction uses the det tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L69-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L69-L90

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

theorem GlobalTheory.CompanionTheory.InertSpan.det_tri (A : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (B : Matrix (Fin N) (Fin N) L)
    (h0 : ∀ i, i ≠ 0 → A i 0 = 0) (hl : ∀ j, j ≠ Fin.last (N + 1) → A (Fin.last (N + 1)) j = 0)
    (hm : ∀ i j, A (mid i) (mid j) = B i j) :
    A.det = A 0 0 * A (Fin.last (N + 1)) (Fin.last (N + 1)) * B.det := by sorry
