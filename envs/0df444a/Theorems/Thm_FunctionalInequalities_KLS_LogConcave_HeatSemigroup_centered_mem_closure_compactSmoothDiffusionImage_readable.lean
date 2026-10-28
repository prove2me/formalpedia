-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_centered_mem_closure_compactSmoothDiffusionImage_readable
-- name    : FunctionalInequalities.KLS.LogConcave.HeatSemigroup.centered_mem_closure_compactSmoothDiffusionImage_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:50.811042+00:00
-- url     : https://prove2.me/theorems/cc2ca884-a315-433e-8321-8e49b01e29b4
-- title:
--   Centered Classes Lie In The Diffusion Image Closure
-- statement:
--   This formalizes the mean-zero density statement recorded as Lemma A.6 of Letwin (arXiv:2607.24164v1), with the reviewed relation recorded as partial.
--
--   Let $V$ be finite-dimensional, let $m$ be an additive Haar measure, let $\nu$ be log-concave with
--
--   $$
--   \nu=m.\operatorname{tilted}(-U),
--   $$
--
--   where $U\in C^1(V)$. If $g\in L^2(\nu)$ has zero mean,
--
--   $$
--   \operatorname{mean}_\nu(g)=0,
--   $$
--
--   then $g$ belongs to the closure in $L^2(\nu)$ of the literal images of smooth compactly supported functions under the diffusion operator `compactSmoothDiffusionImage`:
--
--   $$
--   g\in\overline{\{ -Lf:f\in C_c^\infty(V)\}}.
--   $$
--
--   The conclusion is a closure statement for every mean-zero $L^2$ class; it does not state the Brascamp–Lieb inequality itself.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.HeatSemigroup`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem centered_mem_closure_compactSmoothDiffusionImage
--       {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
--       (hν : FunctionalInequalities.KLS.LogConcave ν) {U : V → ℝ}
--       (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
--       (g : Lp ℝ 2 (ν : Measure V)) (hg : L2.mean ν g = 0) :
--       g ∈ closure (compactSmoothDiffusionImage hU)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Range`](https://prove2.me/theorems/a24adaa9-3bf7-4b4a-8f86-f94e3c7a1ac4).
--
--   Definition modules: [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`mem_closure_range_of_inner_eq_zero`](https://prove2.me/theorems/2b0256b2-bcfd-472f-9590-a4b4f1fd87ee), [`eq_const_mean_of_closedWeightedOperator_eq_zero`](https://prove2.me/theorems/1a8d321f-1b90-4644-b319-efb67dd1e6ce), [`exists_seq_smooth_tendsto_adjointComp_of_localRegularity`](https://prove2.me/theorems/7b48e926-80ae-40b4-a5a6-d33d9c1a1273), [`interior_support_nonempty_of_eq_tilted`](https://prove2.me/theorems/f9e547f0-9041-4fe6-9d08-ab4991b4217f), [`toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`](https://prove2.me/theorems/44e63681-21ce-4775-a563-130ebf063881).
--
--   [Source excerpt, lines 45–50](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Range.lean#L45-L50) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.6. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Range.lean#L44-L115 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Range`, declaration `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.centered_mem_closure_compactSmoothDiffusionImage`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Range

open MeasureTheory Filter Topology Set InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.KLS.LogConcave.HeatSemigroup.centered_mem_closure_compactSmoothDiffusionImage_readable
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
    (hν : FunctionalInequalities.KLS.LogConcave ν) {U : V → ℝ}
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (g : Lp ℝ 2 (ν : Measure V)) (hg : L2.mean ν g = 0) :
    g ∈ closure (compactSmoothDiffusionImage hU) := by sorry
