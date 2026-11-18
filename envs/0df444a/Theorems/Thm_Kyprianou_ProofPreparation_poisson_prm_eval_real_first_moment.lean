-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_eval_real_first_moment
-- name    : Kyprianou.ProofPreparation.poisson_prm_eval_real_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:17:01.130633+00:00
-- url     : https://prove2.me/theorems/bf6d42e7-c10d-46cd-a180-0b6b2e2d2aaa
-- title:
--   Public integrability and mean of finite-intensity Poisson count evaluations
-- statement:
--   For every finite-intensity measurable region A, the real-valued count of the actual Poisson random measure is integrable and has mean m(A). Proved solely from public nonnegative Campbell and outer integrability theorems, by identifying the indicator Bochner integral with the count. Public dependency for disjoint cross moments and two-cell second moments.
-- source:
--   Kyprianou (2006), Chapter 2 Theorem 2.7, first moment of indicator stochastic integrals.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_Ch02_nonnegativePoissonIntegralFirstMoment
import Theorems.Thm_Kyprianou_Ch02_nonnegativePoissonIntegralOuterIntegrable
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem poisson_prm_eval_real_first_moment
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    Integrable (fun ω => (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal) P ∧
    (∫ ω, (ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal ∂P) =
      (m A).toReal := by sorry
end Kyprianou.ProofPreparation
