-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_vecMul_basis
-- name    : GlobalTheory.CompanionTheory.InertSpan.vecMul_basis
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:04:08.710358+00:00
-- url     : https://prove2.me/theorems/2702cf38-531b-4032-b05f-d3679b07fa5b
-- title:
--   Inert Span: vec Mul basis
-- statement:
--   The Inert Span construction uses the vec Mul basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L237-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean#L237-L250

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

theorem GlobalTheory.CompanionTheory.InertSpan.vecMul_basis (q : Fin (N + 2) → L) (g₀ U V C : Matrix (Fin N) (Fin N) L) (r b : Fin N → L) (c y z : L)
    (hy : y ≠ 0) (e : C * (U + V * g₀) = 1) :
    vec3 (0 : L) (z • (r ᵥ* C)) (z * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y) ᵥ*
      mat3 q (fun k => vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k)) (vec3 (0 : L) 0 y) =
      vec3 (0 : L) (z • r) (z * c) := by sorry
