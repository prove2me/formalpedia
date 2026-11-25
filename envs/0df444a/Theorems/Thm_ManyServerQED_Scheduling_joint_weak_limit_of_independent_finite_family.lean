-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_joint_weak_limit_of_independent_finite_family
-- name    : ManyServerQED.Scheduling.joint_weak_limit_of_independent_finite_family
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T21:05:23.681807+00:00
-- url     : https://prove2.me/theorems/9dd01d1d-775d-41d0-a69b-fea9ddd0d72a
-- title:
--   Joint convergence of finite independent families from marginal limits
-- statement:
--   For a finite family of random vectors, suppose each marginal converges in distribution, the coordinates are independent for all sufficiently large system sizes, and the chosen limiting marginals are realized independently. Then the full vector converges jointly in distribution to that independent family.
-- source:
--   Supporting lemma for the proof of Atar, Mandelbaum and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology WithLp

theorem ManyServerQED.Scheduling.joint_weak_limit_of_independent_finite_family {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {k : ℕ} (X : Fin k → ℕ → Ω → E) (Z : Fin k → Ω' → E)
    (hX : ∀ i, TendstoInDistribution (X i) atTop (Z i) (fun _ => P) P')
    (hInd : ∀ᶠ n in atTop, iIndepFun (fun i => X i n) P) (hZ : iIndepFun Z P') :
    TendstoInDistribution (fun n ω i => X i n ω) atTop (fun ω i => Z i ω) (fun _ => P) P' := by sorry
