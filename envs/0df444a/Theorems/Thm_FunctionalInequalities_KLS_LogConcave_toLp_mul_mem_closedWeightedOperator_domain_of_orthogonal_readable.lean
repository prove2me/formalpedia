-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal_readable
-- name    : FunctionalInequalities.KLS.LogConcave.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:41.449981+00:00
-- url     : https://prove2.me/theorems/44e63681-21ce-4775-a563-130ebf063881
-- title:
--   Interior Regularity Of Deficiency Elements
-- statement:
--   This theorem establishes local form-domain membership for deficiency elements.
--
--   Let $V$ be finite-dimensional, let $m$ be an additive Haar measure, let $\nu$ be log-concave with nonempty interior support, and let $U\in C^1(V)$ satisfy $\nu=m.\operatorname{tilted}(-U)$. Let $u\in L^2(\nu)$ satisfy
--
--   $$
--   \langle Af,u\rangle+\langle f,u\rangle=0
--   $$
--
--   for every smooth compactly supported $f$, where $A=\overline{T}^{\dagger}\overline{T}$ and $\overline{T}$ is the closed unit-weight gradient. Then for every smooth compactly supported $\chi$, the class of $\chi u$ belongs to $D(\overline{T})$:
--
--   $$
--   [\chi u]\in D\!\left(\overline{T}_{\nu,m,I}\right).
--   $$
--
--   The class is formed with `memLp_mul_of_contDiff_hasCompactSupport` and `toLp`. This is the local regularity hypothesis used by the operator-core criterion; it does not assert that $u$ itself has a global weak gradient.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal
--       (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : Lp ℝ 2 (ν : Measure V))
--       (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
--         ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
--             ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : Lp ℝ 2 (ν : Measure V)), u⟫ +
--           ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : Lp ℝ 2 (ν : Measure V)), u⟫ = 0)
--       {χ : V → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
--       (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
--         (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/InteriorRegularity`](https://prove2.me/theorems/79e586aa-54d4-4c9a-ac32-31116ce1ca0f).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/LogConcave/HeatSemigroup/Generator`](https://prove2.me/theorems/1303b530-0417-4686-98e2-cba0795ab727), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Energy/WeightedGradient/Core`](https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f), [`KLS/LogConcave/WeightedGradient/Multiplier`](https://prove2.me/theorems/5b6390bb-3865-4ef0-88d2-fa41db26a901).
--
--   Supporting theorems: [`lintegral_enorm_convolution_sq_le`](https://prove2.me/theorems/63807bea-13bd-4a60-93ed-c5b5453cd20a), [`tendsto_eLpNorm_convolution_sub`](https://prove2.me/theorems/3e5007ce-6906-4a04-82a9-55a0bdd821b3), [`integral_laplacian_mul_convolution_eq`](https://prove2.me/theorems/4e49d784-08a5-433a-989e-30d5dbb063cf), [`integral_laplacian_mul_tiltedDensity_mul`](https://prove2.me/theorems/f41686bf-c848-414b-978b-8c5c05a45d74), [`norm_toLp_smul_gradient_le`](https://prove2.me/theorems/498d247b-5ee4-41ec-a4b1-bd5e9cc8d247).
--
--   Previous: [`integral_laplacian_mul_tiltedDensity_mul`](https://prove2.me/theorems/f41686bf-c848-414b-978b-8c5c05a45d74).
--
--   [Source excerpt, lines 555–563](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean#L555-L563) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean#L540-L962 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity`, declaration `FunctionalInequalities.KLS.LogConcave.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity

open MeasureTheory Filter Topology Metric InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace Convolution ENNReal
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
variable (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)

theorem FunctionalInequalities.KLS.LogConcave.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal_readable
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : Lp ℝ 2 (ν : Measure V))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : Lp ℝ 2 (ν : Measure V)), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : Lp ℝ 2 (ν : Measure V)), u⟫ = 0)
    {χ : V → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by sorry
