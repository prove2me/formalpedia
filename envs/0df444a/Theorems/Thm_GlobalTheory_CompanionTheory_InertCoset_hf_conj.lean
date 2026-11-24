-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_conj
-- name    : GlobalTheory.CompanionTheory.InertCoset.hf_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:02:20.808971+00:00
-- url     : https://prove2.me/theorems/a7207356-7f2c-40b8-bec9-2384af315a23
-- title:
--   Inert Coset: hf conj
-- statement:
--   The Inert Coset construction uses the hf conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L17-L21

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
omit [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.CompanionTheory.InertCoset.hf_conj (hσσ : ∀ x, σ (σ x) = x) (x y : Fin n → L) : σ (hf σ x y) = hf σ y x := by sorry
