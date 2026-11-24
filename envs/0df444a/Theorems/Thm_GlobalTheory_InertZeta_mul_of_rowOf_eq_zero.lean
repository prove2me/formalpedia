-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_mul_of_rowOf_eq_zero
-- name    : GlobalTheory.InertZeta.mul_of_rowOf_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:19.416553+00:00
-- url     : https://prove2.me/theorems/d992f4cf-3e53-4ade-9f5c-ab01a4d661ad
-- title:
--   Inert Zeta: mul of row Of eq zero
-- statement:
--   The Inert Zeta construction uses the mul of row Of eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmallRadicalCosetCountOfHeisenberg.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmallRadicalCosetCountOfHeisenberg.lean#L69-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallRadicalCosetCountOfHeisenberg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
variable
  (h1 : ∀ u ∈ radQ σ N, (∀ j, rowOf u j = -σ (colOf u j.rev)) ∧ cornerOf u + σ (cornerOf u) = rowOf u ⬝ᵥ colOf u ∧
      (u ∈ KU σ (N + 2) ↔ (∀ j, rowOf u j ∈ intL L) ∧ cornerOf u ∈ intL L))
  (h2 : ∀ u ∈ radQ σ N, ∀ u' ∈ radQ σ N, rowOf (u * u') = rowOf u + rowOf u' ∧ colOf (u * u') = colOf u + colOf u' ∧
      cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u')
include h1
include h2

theorem GlobalTheory.InertZeta.mul_of_rowOf_eq_zero {u z : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hz : z ∈ radQ σ N) (h : rowOf z = 0) :
    rowOf (u * z) = rowOf u ∧ colOf (u * z) = colOf u ∧ cornerOf (u * z) = cornerOf u + cornerOf z := by sorry
