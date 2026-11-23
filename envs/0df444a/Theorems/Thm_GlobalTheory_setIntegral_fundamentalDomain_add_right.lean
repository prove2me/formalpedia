-- Prove2me | Theorems.Thm_GlobalTheory_setIntegral_fundamentalDomain_add_right
-- name    : GlobalTheory.setIntegral_fundamentalDomain_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:32.200704+00:00
-- url     : https://prove2.me/theorems/d52a4e37-ca11-445c-b53c-c4228acb5668
-- title:
--   Global Theory: set Integral fundamental Domain add right
-- statement:
--   The Global Theory construction uses the set Integral fundamental Domain add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IntegrableOnFundamentalDomainOfContinuous.lean#L13-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IntegrableOnFundamentalDomainOfContinuous.lean#L13-L41

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

theorem GlobalTheory.setIntegral_fundamentalDomain_add_right {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure V) [μ.IsAddHaarMeasure] (b : Module.Basis κ ℝ V)
    (f : V → E) (hb : ∀ γ ∈ Submodule.span ℤ (Set.range b), ∀ v, f (v + γ) = f v) (a : V) :
    ∫ v in ZSpan.fundamentalDomain b, f (v + a) ∂μ = ∫ v in ZSpan.fundamentalDomain b, f v ∂μ := by sorry
