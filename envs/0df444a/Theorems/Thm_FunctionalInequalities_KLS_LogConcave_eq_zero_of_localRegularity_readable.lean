-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_eq_zero_of_localRegularity_readable
-- name    : FunctionalInequalities.KLS.LogConcave.eq_zero_of_localRegularity_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:02.408475+00:00
-- url     : https://prove2.me/theorems/51e4b343-ce48-434b-a25f-137e75ee3400
-- title:
--   Local Form-Domain Regularity Forces Vanishing
-- statement:
--   This theorem is the deficiency-element vanishing criterion for the closed diffusion operator.
--
--   Let $V$ be finite-dimensional and complete, let $m$ be an additive Haar measure, let $\nu$ be log-concave with nonempty interior support, and let $U\in C^1(V)$ satisfy $\nu=m.\operatorname{tilted}(-U)$. Let $u\in L^2(\nu)$ satisfy:
--
--   1. For every smooth compactly supported $f$, the sum of the pairings with $Af$ and $f$ is zero, where $A=\overline{T}^{\dagger}\overline{T}$:
--      $$\langle Af,u\rangle+\langle f,u\rangle=0.$$
--   2. For every smooth compactly supported $\chi$, the class $[\chi u]$ belongs to $D(\overline{T})$.
--
--   Then
--
--   $$
--   u=0$$
--
--   as an $L^2(\nu)$ class, i.e. $u=0$. The local assumption is exactly membership of every compactly supported localization in the form domain; no global gradient or classical regularity of $u$ is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem eq_zero_of_localRegularity
--       (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : (Lp ℝ 2 (ν : Measure V)))
--       (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
--         ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
--           ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
--           ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2 (ν : Measure V))), u⟫ = 0)
--       (hloc : ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
--         (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
--           (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
--       u = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/OperatorCore`](https://prove2.me/theorems/49f2d187-0409-49fa-a861-f4dcb4534ed2).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/LogConcave/HeatSemigroup/Generator`](https://prove2.me/theorems/1303b530-0417-4686-98e2-cba0795ab727), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Energy/WeightedGradient/Core`](https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f), [`KLS/LogConcave/WeightedGradient/Multiplier`](https://prove2.me/theorems/5b6390bb-3865-4ef0-88d2-fa41db26a901).
--
--   Supporting theorems: [`norm_toLp_mul_cutoff_le`](https://prove2.me/theorems/70f87b8e-1e63-4a64-b689-a93e9c786f4e).
--
--   Previous: [`norm_toLp_mul_cutoff_le`](https://prove2.me/theorems/70f87b8e-1e63-4a64-b689-a93e9c786f4e) · Next: [`exists_seq_smooth_tendsto_adjointComp_of_localRegularity`](https://prove2.me/theorems/7b48e926-80ae-40b4-a5a6-d33d9c1a1273).
--
--   [Source excerpt, lines 597–606](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/OperatorCore.lean#L597-L606) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/OperatorCore.lean#L586-L700 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.OperatorCore`, declaration `FunctionalInequalities.KLS.LogConcave.eq_zero_of_localRegularity`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore

open MeasureTheory Filter Topology Metric Set InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}

theorem FunctionalInequalities.KLS.LogConcave.eq_zero_of_localRegularity_readable
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : (Lp ℝ 2 (ν : Measure V)))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2 (ν : Measure V))), u⟫ = 0)
    (hloc : ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
      (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    u = 0 := by sorry
