-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_levi_borel
-- name    : GlobalTheory.CompanionTheory.InertTrans.levi_borel
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:02:58.026542+00:00
-- url     : https://prove2.me/theorems/5aa4aa24-91bf-4e67-bc1c-78ce74bb6162
-- title:
--   Inert Trans: levi borel
-- statement:
--   The Inert Trans construction uses the levi borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SphericalTransitiveOfLevi.lean#L59-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SphericalTransitiveOfLevi.lean#L59-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SphericalTransitiveOfLevi
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertTrans
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertTrans.levi_borel {ϖ : L} {a : ℤ} {g : GU σ N} {m : GU σ (N + 2)} (h : IsLeviElt ϖ a g m) (hg : IsBorelU g) :
    IsBorelU m := by sorry
