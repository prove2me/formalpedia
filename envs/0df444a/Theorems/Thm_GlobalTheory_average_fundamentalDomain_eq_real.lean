-- Prove2me | Theorems.Thm_GlobalTheory_average_fundamentalDomain_eq_real
-- name    : GlobalTheory.average_fundamentalDomain_eq_real
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:04.108004+00:00
-- url     : https://prove2.me/theorems/d1386d43-7707-427a-95f6-e254a911f3c6
-- title:
--   Global Theory: average fundamental Domain eq real
-- statement:
--   The Global Theory construction uses the average fundamental Domain eq real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IntegrableOnFundamentalDomainOfContinuous.lean#L51-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IntegrableOnFundamentalDomainOfContinuous.lean#L51-L66

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

theorem GlobalTheory.average_fundamentalDomain_eq_real {V κ κ' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Fintype κ] [Fintype κ'] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (b : Module.Basis κ ℝ V) (b' : Module.Basis κ' ℝ V)
    (f : V → ℝ) (hf : Continuous f)
    (hb : ∀ γ ∈ Submodule.span ℤ (Set.range b), ∀ v, f (v + γ) = f v)
    (hle : Submodule.span ℤ (Set.range b') ≤ Submodule.span ℤ (Set.range b)) (a : V) :
    ⨍ v in ZSpan.fundamentalDomain b', f (v + a) ∂μ =
      ⨍ v in ZSpan.fundamentalDomain b, f v ∂μ := by sorry
