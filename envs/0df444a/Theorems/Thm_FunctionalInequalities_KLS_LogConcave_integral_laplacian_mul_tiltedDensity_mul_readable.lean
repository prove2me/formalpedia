-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_laplacian_mul_tiltedDensity_mul_readable
-- name    : FunctionalInequalities.KLS.LogConcave.integral_laplacian_mul_tiltedDensity_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:12.548256+00:00
-- url     : https://prove2.me/theorems/f41686bf-c848-414b-978b-8c5c05a45d74
-- title:
--   Weak Equation For A Tilted Density Class
-- statement:
--   This lemma converts an operator orthogonality relation into a Haar-measure weak equation.
--
--   Let $V$ be finite-dimensional, let $m$ be an additive Haar measure, let $\nu$ be log-concave with nonempty interior support, and let $U\in C^1(V)$ satisfy $\nu=m.\operatorname{tilted}(-U)$. Let $u\in L^2(\nu)$ be orthogonal to $(A+1)C_c^\infty(V)$, meaning
--
--   $$
--   \langle Af,u\rangle+\langle f,u\rangle=0
--   $$
--
--   for every smooth compactly supported $f$, with $A=\overline{T}^{\dagger}\overline{T}$. Then every such $f$ satisfies
--
--   $$
--   \int_V (\Delta f)(x)\,\rho(x)u(x)\,dm(x)
--   =
--   \int_V \left\langle\nabla f(x),\rho(x)u(x)\nabla U(x)\right\rangle\,dm(x)
--   +\int_V f(x)\rho(x)u(x)\,dm(x),
--   $$
--
--   where $\rho=\texttt{tiltedDensity}(m,U)$. This is the divergence-form equation used in the interior-regularity argument.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem integral_laplacian_mul_tiltedDensity_mul
--       (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : Lp ℝ 2 (ν : Measure V))
--       (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
--         ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
--             ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : Lp ℝ 2 (ν : Measure V)), u⟫ +
--           ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : Lp ℝ 2 (ν : Measure V)), u⟫ = 0)
--       {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
--       ∫ x, Laplacian.laplacian f x * (tiltedDensity m U x * u x) ∂m =
--         ∫ x, ⟪gradient f x, (tiltedDensity m U x * u x) • gradient U x⟫ ∂m +
--           ∫ x, f x * (tiltedDensity m U x * u x) ∂m
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/InteriorRegularity`](https://prove2.me/theorems/79e586aa-54d4-4c9a-ac32-31116ce1ca0f).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/LogConcave/HeatSemigroup/Generator`](https://prove2.me/theorems/1303b530-0417-4686-98e2-cba0795ab727), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Energy/WeightedGradient/Core`](https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f).
--
--   Previous: [`integral_laplacian_mul_convolution_eq`](https://prove2.me/theorems/4e49d784-08a5-433a-989e-30d5dbb063cf) · Next: [`toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`](https://prove2.me/theorems/44e63681-21ce-4775-a563-130ebf063881).
--
--   [Source excerpt, lines 467–476](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean#L467-L476) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean#L463-L525 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity`, declaration `_private.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity.0.FunctionalInequalities.KLS.LogConcave.integral_laplacian_mul_tiltedDensity_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity

open MeasureTheory Filter Topology Metric InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace Convolution ENNReal
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
variable (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)

theorem FunctionalInequalities.KLS.LogConcave.integral_laplacian_mul_tiltedDensity_mul_readable
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : Lp ℝ 2 (ν : Measure V))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : Lp ℝ 2 (ν : Measure V)), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : Lp ℝ 2 (ν : Measure V)), u⟫ = 0)
    {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∫ x, Laplacian.laplacian f x * (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x) ∂m =
      ∫ x, ⟪gradient f x, (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x) • gradient U x⟫ ∂m +
        ∫ x, f x * (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x) ∂m := by sorry
