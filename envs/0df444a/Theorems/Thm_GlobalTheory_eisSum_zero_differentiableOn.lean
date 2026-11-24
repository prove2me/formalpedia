-- Prove2me | Theorems.Thm_GlobalTheory_eisSum_zero_differentiableOn
-- name    : GlobalTheory.eisSum_zero_differentiableOn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:18:15.051079+00:00
-- url     : https://prove2.me/theorems/cf81b420-a4e0-4638-9c02-976218b2589a
-- title:
--   Global Theory: eis Sum zero differentiable On
-- statement:
--   The Global Theory construction uses the eis Sum zero differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinSeriesLatticeDifferentiableOn.lean#L65-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinSeriesLatticeDifferentiableOn.lean#L65-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NormFderivLeOfClosedBallSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesLatticeDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open Metric Complex
open GlobalTheory
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem GlobalTheory.eisSum_zero_differentiableOn :
    ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F) (k : ℕ),
      (∀ z ∈ upperHalf F, Summable (eisClass 𝔞 𝔟 k 0 z)) →
      DifferentiableOn ℂ (eisSum 𝔞 𝔟 k 0) (upperHalf F) := by sorry
