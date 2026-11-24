-- Prove2me | Theorems.Thm_GlobalTheory_integrableOn_fundamentalDomain_of_continuous
-- name    : GlobalTheory.integrableOn_fundamentalDomain_of_continuous
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:56:28.110732+00:00
-- url     : https://prove2.me/theorems/3c376601-1aab-4db7-9c12-b4d5c5258456
-- title:
--   Global Theory: integrable On fundamental Domain of continuous
-- statement:
--   The Global Theory construction uses the integrable On fundamental Domain of continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IntegrableOnFundamentalDomainOfContinuous.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IntegrableOnFundamentalDomainOfContinuous.lean#L43-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MeasureTheory
variable {V κ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Fintype κ]

theorem GlobalTheory.integrableOn_fundamentalDomain_of_continuous {E : Type} [NormedAddCommGroup E]
    (μ : Measure V) [μ.IsAddHaarMeasure] (b : Module.Basis κ ℝ V)
    (f : V → E) (hf : Continuous f) : IntegrableOn f (ZSpan.fundamentalDomain b) μ := by sorry
