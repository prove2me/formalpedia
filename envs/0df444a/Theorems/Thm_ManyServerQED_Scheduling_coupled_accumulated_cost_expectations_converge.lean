-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_coupled_accumulated_cost_expectations_converge
-- name    : ManyServerQED.Scheduling.coupled_accumulated_cost_expectations_converge
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:55:32.630512+00:00
-- url     : https://prove2.me/theorems/17c714bc-62dd-5af5-9896-79db1f9466c9
-- title:
--   Convergence of coupled accumulated cost expectations
-- statement:
--   Suppose that the running-cost coordinate of the joint observation path is nonnegative and represents a prelimit cost, with a uniform moment above order one. Then the limiting cost coordinate is integrable and its expectation is the limit of the prelimit cost expectations.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_nonnegative_cost_expectation_from_ae_limit_and_moment
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.coupled_accumulated_cost_expectations_converge {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) (hs : Tendsto s atTop atTop)
    (T : ℝ≥0) (p : ℝ) (hp : 1 < p) (K : ℝ≥0∞) (hK : K < ⊤)
    (e : ℕ → Ω → ℝ≥0∞)
    (hCost : ∀ᶠ n in atTop, ∀ ω,
        0 ≤ Z n ω T (Fin.natAdd (k+k+k) (0 : Fin 2)) ∧
        ENNReal.ofReal (Z n ω T (Fin.natAdd (k+k+k) (0 : Fin 2))) = e n ω)
    (hMom : ∀ᶠ n in atTop, (∫⁻ ω, e n ω ^ p ∂P) ≤ K) :
    Integrable (d.runningCost T) d.Q ∧
      Tendsto (fun j => ∫⁻ ω, e (s (d.r j)) ω ∂P) atTop
        (𝓝 (ENNReal.ofReal (∫ ω, d.runningCost T ω ∂d.Q))) := by sorry
