-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_smul
-- name    : GlobalTheory.CompanionTheory.InertCoset.hf_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:54:38.404141+00:00
-- url     : https://prove2.me/theorems/4fa5a770-ba79-49b6-9a1a-098479ba001a
-- title:
--   Inert Coset: hf smul
-- statement:
--   The Inert Coset construction uses the hf smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L36-L39

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

theorem GlobalTheory.CompanionTheory.InertCoset.hf_smul (c c' : L) (x y : Fin n → L) : hf σ (c • x) (c' • y) = σ c * c' * hf σ x y := by sorry
