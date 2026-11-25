-- Prove2me | Theorems.Thm_GlobalTheory_IsogenySum_pairing_density_continuous
-- name    : GlobalTheory.IsogenySum.pairing_density_continuous
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:10:08.473463+00:00
-- url     : https://prove2.me/theorems/60c57c70-19a5-4251-889e-12453e51df6b
-- title:
--   Isogeny Sum: pairing density continuous
-- statement:
--   The Isogeny Sum construction uses the pairing density continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ContinuousThetaSectionPointwiseNormSq.lean#L141-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ContinuousThetaSectionPointwiseNormSq.lean#L141-L147

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

theorem GlobalTheory.IsogenySum.pairing_density_continuous {F : EuclideanSpace ℂ ι → ℂ} (hF : Differentiable ℂ F)
    (y y' : EuclideanSpace ℂ ι) : Continuous fun v =>
      U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v)) := by sorry
