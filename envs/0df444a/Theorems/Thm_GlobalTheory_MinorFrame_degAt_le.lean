-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_degAt_le
-- name    : GlobalTheory.MinorFrame.degAt_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:36.306633+00:00
-- url     : https://prove2.me/theorems/32e4b2be-fd7c-43c4-8cb5-c36a12435c0e
-- title:
--   Minor Frame: deg At le
-- statement:
--   The Minor Frame construction uses the deg At le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralDetCharacterFockColumnSubstitutionEqZero.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralDetCharacterFockColumnSubstitutionEqZero.lean#L41-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralDetCharacterFockColumnSubstitutionEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.degAt_le {d a : ℕ} (τ₀ : ι) (t : Var ι d a →₀ ℕ) : degAt τ₀ t ≤ t.sum fun _ e => e := by sorry
