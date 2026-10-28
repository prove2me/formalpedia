-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_norm_toLp_mul_cutoff_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.norm_toLp_mul_cutoff_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:32.405465+00:00
-- url     : https://prove2.me/theorems/70f87b8e-1e63-4a64-b689-a93e9c786f4e
-- title:
--   Scaled Cutoff Estimate
-- statement:
--   This auxiliary lemma gives a quantitative cutoff estimate for a closed weighted-gradient domain.
--
--   Let $V$ be finite-dimensional and complete, let $m$ be an additive Haar measure, let $\nu$ be log-concave with nonempty interior support, and let $U\in C^1(V)$ satisfy $\nu=m.\operatorname{tilted}(-U)$. Let $u\in L^2(\nu)$ satisfy:
--
--   1. For every smooth compactly supported $f$, the pairing of $u$ with $(A+1)f$ is zero, where $A=\overline{T}^{\dagger}\overline{T}$ is represented by `adjointComp`.
--   2. For every smooth compactly supported multiplier $\chi$, the class $\chi u$ belongs to $D(\overline{T})$.
--
--   If $r>0$, $M\ge0$, and the cutoff satisfies $\|\nabla\chi_r(y)\|\le M/r$ for all $y$, then
--
--   $$
--   \|[\chi_r u]\|_{L^2(\nu)}\le \frac{M}{r}\,\|u\|_{L^2(\nu)}.
--   $$
--
--   The cutoff family and the domain are represented by `cutoff`, `toLp`, and `closedWeightedOperator`. This is a technical estimate used to pass from local domain membership to global vanishing.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem norm_toLp_mul_cutoff_le
--       (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : (Lp ℝ 2 (ν : Measure V)))
--       (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
--         ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
--           ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
--           ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2 (ν : Measure V))), u⟫ = 0)
--       (hloc : ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
--         (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
--           (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
--       {r M : ℝ} (hr : 0 < r) (hM0 : 0 ≤ M)
--       (hM : ∀ y : V, ‖gradient (cutoff (V := V) r) y‖ ≤ M / r) :
--       ‖(memLp_mul_of_contDiff_hasCompactSupport (ν := ν) (contDiff_cutoff r)
--           (hasCompactSupport_cutoff hr) u).toLp _‖ ≤ (M / r) * ‖u‖
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/OperatorCore`](https://prove2.me/theorems/49f2d187-0409-49fa-a861-f4dcb4534ed2).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/LogConcave/HeatSemigroup/Generator`](https://prove2.me/theorems/1303b530-0417-4686-98e2-cba0795ab727), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Energy/WeightedGradient/Core`](https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f), [`KLS/LogConcave/WeightedGradient/Multiplier`](https://prove2.me/theorems/5b6390bb-3865-4ef0-88d2-fa41db26a901).
--
--   Supporting theorems: [`weightedLaplacian_eq_zero_of_notMem_tsupport`](https://prove2.me/theorems/b381f334-820c-4611-a1c1-f11888c8bc19), [`exists_mem_domain_closedWeightedOperator_toLp_mul`](https://prove2.me/theorems/465ec746-a212-4a4a-a2ab-2d9cca0a20ec), [`exists_seq_smooth_tendsto_graph`](https://prove2.me/theorems/c7be6850-4704-4912-95fa-1692fa90fd5a).
--
--   Next: [`eq_zero_of_localRegularity`](https://prove2.me/theorems/51e4b343-ce48-434b-a25f-137e75ee3400).
--
--   [Source excerpt, lines 190–202](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/OperatorCore.lean#L190-L202) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/OperatorCore.lean#L188-L584 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.OperatorCore`, declaration `_private.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.OperatorCore.0.FunctionalInequalities.KLS.LogConcave.norm_toLp_mul_cutoff_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore

open MeasureTheory Filter Topology Metric Set InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}

theorem FunctionalInequalities.KLS.LogConcave.norm_toLp_mul_cutoff_le_readable
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : (Lp ℝ 2 (ν : Measure V)))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2 (ν : Measure V))), u⟫ = 0)
    (hloc : ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
      (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {r M : ℝ} (hr : 0 < r) (hM0 : 0 ≤ M)
    (hM : ∀ y : V, ‖gradient (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) y‖ ≤ M / r) :
    ‖(memLp_mul_of_contDiff_hasCompactSupport (ν := ν) (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff r)
        (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff hr) u).toLp _‖ ≤ (M / r) * ‖u‖ := by sorry
