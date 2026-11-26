-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_joint_observation_finite_laws_give_filtered_brownian
-- name    : ManyServerQED.Scheduling.joint_observation_finite_laws_give_filtered_brownian
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:48:21.785032+00:00
-- url     : https://prove2.me/theorems/5fe7bb1e-3c10-4d5b-a403-aeec50de3711
-- title:
--   Finite laws of joint observations identify a Brownian filtration
-- statement:
--   For a continuous limit of queue observations, suppose its noise has the finite-dimensional distributions of a vector with independent Brownian coordinates, and each finite family of future noise increments is independent of each finite family of past observations. The limit noise is then Brownian for the natural filtration of the joint observations, for which the limit state is adapted.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.joint_observation_finite_laws_give_filtered_brownian {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {k : ℕ} {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s)
    (V : ℝ≥0 → Ω' → Fin k → ℝ)
    (hV : ∀ i, IsBrownianReal (fun t ω => V t ω i) Q)
    (hVi : iIndepFun (fun i ω (t : ℝ≥0) => V t ω i) Q)
    (hVm : ∀ t, Measurable (V t))
    (hLaw : ∀ (m : ℕ) (τ : Fin m → ℝ≥0),
      IdentDistrib (fun ω j => d.noise (τ j) ω) (fun ω j => V (τ j) ω) d.Q Q)
    (hInd : ∀ (t : ℝ≥0) (a b : ℕ) (p : Fin a → ℝ≥0) (q : Fin b → ℝ≥0),
      (∀ j, p j ≤ t) →
      IndepFun (fun ω j => d.limit ω (p j)) (fun ω j => d.noise (t+q j) ω-d.noise t ω) d.Q) :
    ∃ F : Filtration ℝ≥0 d.mΩ', IsStdFBrownian d.Q F d.noise ∧
      ∀ t, Measurable[F t] (d.state t) := by sorry
