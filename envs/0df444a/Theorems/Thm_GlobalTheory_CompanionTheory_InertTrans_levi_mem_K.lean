-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_levi_mem_K
-- name    : GlobalTheory.CompanionTheory.InertTrans.levi_mem_K
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:04:10.566361+00:00
-- url     : https://prove2.me/theorems/eeb485b5-c71e-4963-86a0-ef4de4da6117
-- title:
--   Inert Trans: levi mem K
-- statement:
--   The Inert Trans construction uses the levi mem K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SphericalTransitiveOfLevi.lean#L76-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SphericalTransitiveOfLevi.lean#L76-L90

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

theorem GlobalTheory.CompanionTheory.InertTrans.levi_mem_K {ϖ : L} {g : GU σ N} {m : GU σ (N + 2)} (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (h : IsLeviElt ϖ 0 g m) (hg : g ∈ KU σ N) : m ∈ KU σ (N + 2) := by sorry
