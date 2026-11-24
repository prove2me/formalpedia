-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_colOf_eq_zero
-- name    : GlobalTheory.InertZeta.colOf_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:19:45.046065+00:00
-- url     : https://prove2.me/theorems/8b049dc7-e5bc-45b3-a137-89cc75eada4f
-- title:
--   Inert Zeta: col Of eq zero
-- statement:
--   The Inert Zeta construction uses the col Of eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmallRadicalCosetCountOfHeisenberg.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmallRadicalCosetCountOfHeisenberg.lean#L41-L42

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

theorem GlobalTheory.InertZeta.colOf_eq_zero {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) (h : rowOf u = 0) : colOf u = 0 := by sorry
