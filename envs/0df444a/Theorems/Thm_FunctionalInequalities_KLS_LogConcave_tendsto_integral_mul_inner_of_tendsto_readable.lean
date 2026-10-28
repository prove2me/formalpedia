-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_tendsto_integral_mul_inner_of_tendsto_readable
-- name    : FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_inner_of_tendsto_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:58.650063+00:00
-- url     : https://prove2.me/theorems/af848101-2a6e-4098-8b0e-6563207a68d5
-- title:
--   Convergence Of Haar Pairings For Vector Fields
-- statement:
--   This theorem transfers $L^2(\nu;V)$ convergence of vector fields to convergence of localized Haar pairings.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, let $\nu$ be a probability measure, and let $U:V\to\mathbb R$ be continuous with $\nu=m.\operatorname{tilted}(-U)$. Suppose $G_n:V\to V$ are all in $L^2(\nu;V)$ and their `MemLp.toLp` classes converge to $F\in L^2(\nu;V)$. If $\psi:V\to\mathbb R$ is continuous and compactly supported, then for every direction $w\in V$,
--
--   $$
--   \int_V \psi(x)\langle G_n(x),w\rangle\,dm(x)
--   \longrightarrow
--   \int_V \psi(x)\langle F(x),w\rangle\,dm(x).
--   $$
--
--   The result is useful when passing from graph approximations in $L^2(\nu;V)$ to weak identities written with respect to the Haar measure. The compact support of $\psi$ supplies the required local integrability.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_integral_mul_inner_of_tendsto (hνU : (ν : Measure V) = m.tilted (-U))
--       (hU : Continuous U) {G : ℕ → V → V} (hG : ∀ n, MemLp (G n) 2 (ν : Measure V))
--       {F : Lp V 2 (ν : Measure V)} (hlim : Tendsto (fun n => (hG n).toLp (G n)) atTop (𝓝 F))
--       {ψ : V → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (w : V) :
--       Tendsto (fun n => ∫ x, ψ x * ⟪G n x, w⟫ ∂m) atTop (𝓝 (∫ x, ψ x * ⟪F x, w⟫ ∂m))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeightedGradient/Kernel`](https://prove2.me/theorems/53a4cc1e-e3fe-4459-bbf4-e862b9c35c22).
--
--   Supporting theorems: [`integral_eq_integral_mul_exp`](https://prove2.me/theorems/e50ba0fe-194c-4fab-a951-2f7b7b282f0a).
--
--   Previous: [`tendsto_integral_mul_of_tendsto`](https://prove2.me/theorems/0ead0018-76f8-4e4a-918c-0de12ef6b171) · Next: [`integral_mul_fderiv_eq_neg_integral_mul_inner`](https://prove2.me/theorems/7c322f0f-17ab-4ef7-afc1-582bee9c53ac).
--
--   [Source excerpt, lines 234–238](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L234-L238) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L232-L319 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel`, declaration `FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_inner_of_tendsto`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}

theorem FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_inner_of_tendsto_readable (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U) {G : ℕ → V → V} (hG : ∀ n, MemLp (G n) 2 (ν : Measure V))
    {F : Lp V 2 (ν : Measure V)} (hlim : Tendsto (fun n => (hG n).toLp (G n)) atTop (𝓝 F))
    {ψ : V → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (w : V) :
    Tendsto (fun n => ∫ x, ψ x * ⟪G n x, w⟫ ∂m) atTop (𝓝 (∫ x, ψ x * ⟪F x, w⟫ ∂m)) := by sorry
