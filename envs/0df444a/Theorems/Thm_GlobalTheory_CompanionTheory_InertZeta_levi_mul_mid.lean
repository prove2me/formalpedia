-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_levi_mul_mid
-- name    : GlobalTheory.CompanionTheory.InertZeta.levi_mul_mid
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:33.851014+00:00
-- url     : https://prove2.me/theorems/c344192b-e46e-487d-a26e-09d7fae70cd1
-- title:
--   Inert Zeta: levi mul mid
-- statement:
--   The Inert Zeta construction uses the levi mul mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetInjective.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetInjective.lean#L51-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetInjective
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
variable {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertZeta.levi_mul_mid {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (i j : Fin N) :
    mat (x * y) (mid i) (mid j) = ∑ k, mat x (mid i) (mid k) * mat y (mid k) (mid j) := by sorry
