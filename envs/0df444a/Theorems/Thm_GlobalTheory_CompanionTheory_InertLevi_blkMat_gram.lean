-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_blkMat_gram
-- name    : GlobalTheory.CompanionTheory.InertLevi.blkMat_gram
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:04.319815+00:00
-- url     : https://prove2.me/theorems/bdc502e5-020b-481c-b2c7-eb47d6003dfc
-- title:
--   Inert Levi: blk Mat gram
-- statement:
--   The Inert Levi construction uses the blk Mat gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LeviDecompositionExists.lean#L47-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LeviDecompositionExists.lean#L47-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LeviDecompositionExists
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLevi
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertLevi.blkMat_gram {x y : L} (hxy : σ x * y = 1) (hyx : σ y * x = 1) {A : Matrix (Fin N) (Fin N) L}
    (hA : cT σ A * antiJ L N * A = antiJ L N) :
    cT σ (blkMat x y A) * antiJ L (N + 2) * blkMat x y A = antiJ L (N + 2) := by sorry
