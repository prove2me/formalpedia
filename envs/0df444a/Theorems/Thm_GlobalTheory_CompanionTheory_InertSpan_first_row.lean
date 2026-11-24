-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_first_row
-- name    : GlobalTheory.CompanionTheory.InertSpan.first_row
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:03:39.781803+00:00
-- url     : https://prove2.me/theorems/1a977fb2-3b80-4109-9161-16747976d8b3
-- title:
--   Inert Span: first row
-- statement:
--   The Inert Span construction uses the first row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L173-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L173-L229

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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertSpan.first_row {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (a : ℤ) (r : Fin N → L) (c : L)
    (R : Submodule (intL L) (Fin (N + 2) → L)) (he : vec3 (1 : L) 0 0 ∈ R)
    (hA : vec3 (ϖ ^ a) (ϖ ^ a • r) (ϖ ^ a * c) ∈ R) (hl : vec3 (0 : L) 0 1 ∈ R)
    (hD : vec3 (0 : L) 0 (ϖ ^ (-a)) ∈ R) :
    ∃ q : Fin (N + 2) → L, Valued.v (q 0) = WithZero.exp ((-a).toNat : ℤ) ∧ q ∈ R ∧
      vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) ∈ R ∧
      (∃ w, Valued.v w = WithZero.exp (a.toNat : ℤ) ∧ vec3 (0 : L) 0 w ∈ R) ∧
      ∀ R' : Submodule (intL L) (Fin (N + 2) → L), q ∈ R' →
        vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) ∈ R' →
        vec3 (1 : L) 0 0 ∈ R' ∧ vec3 (ϖ ^ a) (ϖ ^ a • r) (ϖ ^ a * c) ∈ R' := by sorry
