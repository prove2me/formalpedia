-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteCompensatedFutureIncrementIndependentMeanV1
-- name    : Kyprianou.Ch02.prmFiniteCompensatedFutureIncrementIndependentMeanV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:49:37.169894+00:00
-- url     : https://prove2.me/theorems/c6ddcb3f-8f47-448c-b2a4-08508c21a4f7
-- title:
--   Future compensated finite-band integral increments are independent of the completed past and centred
-- statement:
--   For an actual finite-intensity KLS Poisson random measure and its completed right-continuous natural filtration, the centred real-valued signed marked-integral increment between s and t is independent of the time-s completed sigma-algebra, and its mean is exactly zero. Both assertions are required, including at s=t. The completion and right-continuity require a genuine transfer of PRM past/future independence; the nonnegative and negative marked pieces must be integrable and Campbell centring must be justified for the actual KLS random measure. This is an exact substantive missing stochastic obligation in Lemma 2.9, not a martingale conclusion assumed as a hypothesis.
-- source:
--   Kyprianou (2006) Chapter 2, Lemma 2.9; finite-intensity compensated Poisson random measures under completed right-continuous filtration.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteCompensatedFutureIncrementIndependentMeanV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B))
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    ∀ (s t : ℝ≥0), s ≤ t →
      let M : ℝ≥0 → Ω → ℝ := fun r ω =>
        (∫ z in (Set.Ioc (0 : ℝ) (r : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
          (r : ℝ) * (∫ x in B, x ∂ν)
      let D : Ω → ℝ := fun ω => M t ω - M s ω
      ProbabilityTheory.Indep (MeasurableSpace.comap D inferInstance) (ℱ s) P ∧
        (∫ ω, D ω ∂P) = 0 := by
  sorry
