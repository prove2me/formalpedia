-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_le_of_lt_exp
-- name    : GlobalTheory.CompanionTheory.InertLen.le_of_lt_exp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:01:43.092525+00:00
-- url     : https://prove2.me/theorems/35a4f425-10e5-47a1-98ab-ce2e419f0615
-- title:
--   Inert Len: le of lt exp
-- statement:
--   The Inert Len construction uses the le of lt exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/PointwiseOfSpanHeisenberg.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/PointwiseOfSpanHeisenberg.lean#L35-L43

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

theorem GlobalTheory.CompanionTheory.InertLen.le_of_lt_exp {x : WithZero (Multiplicative ℤ)} {k : ℕ} (h : x < WithZero.exp ((k + 1 : ℕ) : ℤ)) :
    x ≤ WithZero.exp (k : ℤ) := by sorry
