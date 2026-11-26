-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_weak_convergence_from_coupled_observations
-- name    : ManyServerQED.Scheduling.weak_convergence_from_coupled_observations
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:08:27.807214+00:00
-- url     : https://prove2.me/theorems/69fb8109-0d11-4fb3-905d-61f783b33f0a
-- title:
--   Weak convergence of observations under equal-law coupling
-- statement:
--   Suppose each original variable and its coupled copy have the same law. If a measurable observation of the coupled copies converges almost surely, then the same observations of the original variables converge in distribution to the coupled limit.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology

theorem ManyServerQED.Scheduling.weak_convergence_from_coupled_observations
    {Ω Ω' E D : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace D] [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → D) (X' : ℕ → Ω' → D)
    (hLaw : ∀ n, IdentDistrib (X n) (X' n) P P')
    (G : D → E) (hG : Measurable G)
    (L : Ω' → E) (hL : AEMeasurable L P')
    (hlim : ∀ᵐ ω ∂P', Tendsto (fun n => G (X' n ω)) atTop (𝓝 (L ω))) :
    TendstoInDistribution (fun n ω => G (X n ω)) atTop L (fun _ => P) P' := by sorry
