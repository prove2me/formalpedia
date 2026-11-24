-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_exists_col
-- name    : GlobalTheory.CompanionTheory.InertCoset.exists_col
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:02:31.927046+00:00
-- url     : https://prove2.me/theorems/0153e5c3-4f2e-4ff7-ab84-aa77da4cc7be
-- title:
--   Inert Coset: exists col
-- statement:
--   The Inert Coset construction uses the exists col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L424-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L424-L502

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem GlobalTheory.CompanionTheory.InertCoset.exists_col {ϖ : L} {q N : ℕ} (hU : IsUnramInv ϖ σ q) (g : GU σ (N + 2)) :
    ∃ s : ℤ, ∃ k ∈ KU σ (N + 2), ∀ i, mat (g * k) i 0 = ϖ ^ s * (Pi.single 0 1 : Fin (N + 2) → L) i := by sorry
