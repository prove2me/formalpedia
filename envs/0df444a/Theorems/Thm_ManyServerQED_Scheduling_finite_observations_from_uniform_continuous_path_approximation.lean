-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_finite_observations_from_uniform_continuous_path_approximation
-- name    : ManyServerQED.Scheduling.finite_observations_from_uniform_continuous_path_approximation
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:32:23.105049+00:00
-- url     : https://prove2.me/theorems/619a875c-15da-4c1f-b7d3-fced37470e57
-- title:
--   Finite observations from continuous path approximations
-- statement:
--   Let random paths on the continuous unit-interval path space converge in distribution. Evaluate each path at a finite vector of deterministic times converging to a limit vector, after projecting the times onto the unit interval. A fixed multiple of these evaluations and any random vector differing from it by a term converging to zero in probability have the same limiting distribution.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_DurrettProbability_Donsker
open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open DurrettProbability

theorem ManyServerQED.Scheduling.finite_observations_from_uniform_continuous_path_approximation {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Y : ℕ → Ω → PathSpace) (Z : Ω' → PathSpace)
    (hY : TendstoInDistribution Y atTop Z (fun _ => P) P')
    {m : ℕ} (d : ℕ → Fin m → ℝ) (e : Fin m → ℝ)
    (hd : Tendsto d atTop (𝓝 e)) (c : ℝ)
    (Q : ℕ → Ω → Fin m → ℝ) (hQ : ∀ n, AEMeasurable (Q n) P)
    (hA : ∀ ε > (0:ℝ), Tendsto (fun n => P {ω | ∃ i : Fin m,
      ε ≤ |Q n ω i - c*Y n ω (Set.projIcc 0 1 zero_le_one (d n i))|}) atTop (𝓝 0)) :
    TendstoInDistribution Q atTop
      (fun ω i => c * Z ω (Set.projIcc 0 1 zero_le_one (e i))) (fun _ => P) P' := by sorry
