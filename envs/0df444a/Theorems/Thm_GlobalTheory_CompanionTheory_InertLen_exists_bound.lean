-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_exists_bound
-- name    : GlobalTheory.CompanionTheory.InertLen.exists_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:01:53.597392+00:00
-- url     : https://prove2.me/theorems/87c432a2-4c49-451d-8f0d-0314fa3ce569
-- title:
--   Inert Len: exists bound
-- statement:
--   The Inert Len construction uses the exists bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/PointwiseOfSpanHeisenberg.lean#L58-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/PointwiseOfSpanHeisenberg.lean#L58-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_PointwiseOfSpanHeisenberg
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLen
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.CompanionTheory.InertLen.exists_bound {ι : Type} [Fintype ι] [Nonempty ι] (ρ : ι → L) :
    ∃ e : ℕ, (∀ i, Valued.v (ρ i) ≤ WithZero.exp (e : ℤ)) ∧ (e = 0 ∨ ∃ i, Valued.v (ρ i) = WithZero.exp (e : ℤ)) := by sorry
