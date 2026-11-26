-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_continuous_limit_can_be_realized_on_a_path_coupling
-- name    : ManyServerQED.Scheduling.continuous_limit_can_be_realized_on_a_path_coupling
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:38:44.388394+00:00
-- url     : https://prove2.me/theorems/0b40295d-2e2c-5bdc-8ce0-867a7a2211b7
-- title:
--   A continuous limiting law supplies a continuous representative on the coupling
-- statement:
--   Suppose a càdlàg process coupling converges uniformly on compact intervals and the limiting evaluation law admits a continuous representative. Then the coupling can be realized with measurable evaluations of the rows and a limit continuous on every nonnegative sample path.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Reiman84.QueueLength BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.continuous_limit_can_be_realized_on_a_path_coupling {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (P : Measure Ω) (P' : Measure Ω')
    (X : ℕ → Ω → ℝ → Fin k → ℝ) (x : Ω' → ℝ → Fin k → ℝ)
    (hx : ∀ ω, ContinuousOn (x ω) (Ici (0:ℝ)))
    (h : CouplingConverges P P' X x) :
    ∃ (Λ : Type) (_ : MeasurableSpace Λ) (Q : Measure Λ)
      (Y : ℕ → Λ → ℝ → Fin k → ℝ) (v : Λ → ℝ → Fin k → ℝ),
      IsProbabilityMeasure Q ∧
      (∀ᶠ n in atTop, IdentDistrib (fun ω (t : ℝ≥0) => Y n ω t)
        (fun ω (t : ℝ≥0) => X n ω t) Q P) ∧
      IdentDistrib (fun ω (t : ℝ≥0) => v ω t) (fun ω (t : ℝ≥0) => x ω t) Q P' ∧
      (∀ n ω i, IsCadlag (fun t => Y n ω t i)) ∧
      (∀ ω, ContinuousOn (v ω) (Ici (0:ℝ))) ∧
      (∀ t : ℝ≥0, Measurable (fun ω => v ω t)) ∧
      ∀ᵐ ω ∂Q, ∀ T : ℝ, 0 ≤ T → Tendsto (fun n => supDist (Y n ω) (v ω) T) atTop (𝓝 0) := by sorry
