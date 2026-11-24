-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_isLeviElt_mul
-- name    : GlobalTheory.CompanionTheory.InertCoset.isLeviElt_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:02:22.897926+00:00
-- url     : https://prove2.me/theorems/1f890057-94ce-4f5a-989f-15f6303091da
-- title:
--   Inert Coset: is Levi Elt mul
-- statement:
--   The Inert Coset construction uses the is Levi Elt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L508-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetSurjectiveOfLevi.lean#L508-L528

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
variable {N : ℕ} {ϖ : L} {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)}

theorem GlobalTheory.CompanionTheory.InertCoset.isLeviElt_mul (h0 : ϖ ≠ 0) (h : IsLeviElt ϖ a g m) (h' : IsLeviElt ϖ a' g' m') :
    IsLeviElt ϖ (a + a') (g * g') (m * m') := by sorry
