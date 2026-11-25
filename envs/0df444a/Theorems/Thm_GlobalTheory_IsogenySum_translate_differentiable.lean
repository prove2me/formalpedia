-- Prove2me | Theorems.Thm_GlobalTheory_IsogenySum_translate_differentiable
-- name    : GlobalTheory.IsogenySum.translate_differentiable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:08:43.726193+00:00
-- url     : https://prove2.me/theorems/842a3ae0-9d54-42ad-b7a4-6fa63e88ec26
-- title:
--   Isogeny Sum: translate differentiable
-- statement:
--   The Isogeny Sum construction uses the translate differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ContinuousThetaSectionPointwiseNormSq.lean#L132-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ContinuousThetaSectionPointwiseNormSq.lean#L132-L139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open GlobalTheory.IsogenySum
open FockTranslation
variable {ι : Type} [Fintype ι]
variable (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
  (hU : ∀ (q : ℕ) a F v, U q a F v =
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
include hU

theorem GlobalTheory.IsogenySum.translate_differentiable {F : EuclideanSpace ℂ ι → ℂ} (hF : Differentiable ℂ F)
    (a : EuclideanSpace ℂ ι) : Differentiable ℂ (U 1 a F) := by sorry
