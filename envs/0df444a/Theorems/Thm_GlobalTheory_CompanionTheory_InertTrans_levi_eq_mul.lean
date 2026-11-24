-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_levi_eq_mul
-- name    : GlobalTheory.CompanionTheory.InertTrans.levi_eq_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:04:32.558833+00:00
-- url     : https://prove2.me/theorems/d59cc22e-1d6a-4bf1-bc5c-52226aa61d34
-- title:
--   Inert Trans: levi eq mul
-- statement:
--   The Inert Trans construction uses the levi eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SphericalTransitiveOfLevi.lean#L92-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SphericalTransitiveOfLevi.lean#L92-L103

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

theorem GlobalTheory.CompanionTheory.InertTrans.levi_eq_mul {ϖ : L} {a : ℤ} {b k : GU σ N} {mb mk m : GU σ (N + 2)} (hb : IsLeviElt ϖ a b mb)
    (hk : IsLeviElt ϖ 0 k mk) (hm : IsLeviElt ϖ a (b * k) m) : m = mb * mk := by sorry
