-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_tendsto_integral_mul_of_tendsto_readable
-- name    : FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_of_tendsto_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:05.578987+00:00
-- url     : https://prove2.me/theorems/0ead0018-76f8-4e4a-918c-0de12ef6b171
-- title:
--   Convergence Of Haar Pairings For Scalar Functions
-- statement:
--   This theorem transfers scalar $L^2(\nu)$ convergence to convergence of Haar integrals against compactly supported weights.
--
--   Let $V$ be a finite-dimensional real vector space with the stated Borel and topological structures, let $m$ be an additive Haar measure, let $\nu$ be a probability measure, and let $U:V\to\mathbb R$ be continuous with $\nu=m.\operatorname{tilted}(-U)$. Suppose $g_n\in L^2(\nu)$ and the classes of $g_n$ converge to $f\in L^2(\nu)$. For every continuous compactly supported $\psi:V\to\mathbb R$,
--
--   $$
--   \int_V g_n(x)\psi(x)\,dm(x)
--   \longrightarrow
--   \int_V f(x)\psi(x)\,dm(x).
--   $$
--
--   This is a technical localization lemma used to pass $L^2(\nu)$ limits through Haar integrals. No global integrability of the functions with respect to $m$ is required beyond what follows from the tilted-law and compact-support hypotheses.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_integral_mul_of_tendsto (hνU : (ν : Measure V) = m.tilted (-U))
--       (hU : Continuous U) {g : ℕ → V → ℝ} (hg : ∀ n, MemLp (g n) 2 (ν : Measure V))
--       {f : Lp ℝ 2 (ν : Measure V)} (hlim : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 f))
--       {ψ : V → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
--       Tendsto (fun n => ∫ x, g n x * ψ x ∂m) atTop (𝓝 (∫ x, f x * ψ x ∂m))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeightedGradient/Kernel`](https://prove2.me/theorems/53a4cc1e-e3fe-4459-bbf4-e862b9c35c22).
--
--   Supporting theorems: [`integrable_exp_neg_of_eq_tilted`](https://prove2.me/theorems/df26f9df-caa5-4567-8468-df64dde52e70), [`integral_eq_integral_mul_exp`](https://prove2.me/theorems/e50ba0fe-194c-4fab-a951-2f7b7b282f0a).
--
--   Previous: [`restrict_le_smul_of_eq_tilted`](https://prove2.me/theorems/7744a7a5-331d-4220-a88d-91325cd3a0c8) · Next: [`tendsto_integral_mul_inner_of_tendsto`](https://prove2.me/theorems/af848101-2a6e-4098-8b0e-6563207a68d5).
--
--   [Source excerpt, lines 148–152](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L148-L152) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L146-L230 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel`, declaration `FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_of_tendsto`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel

open MeasureTheory Filter Topology InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}

theorem FunctionalInequalities.KLS.LogConcave.tendsto_integral_mul_of_tendsto_readable (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U) {g : ℕ → V → ℝ} (hg : ∀ n, MemLp (g n) 2 (ν : Measure V))
    {f : Lp ℝ 2 (ν : Measure V)} (hlim : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 f))
    {ψ : V → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ x, g n x * ψ x ∂m) atTop (𝓝 (∫ x, f x * ψ x ∂m)) := by sorry
