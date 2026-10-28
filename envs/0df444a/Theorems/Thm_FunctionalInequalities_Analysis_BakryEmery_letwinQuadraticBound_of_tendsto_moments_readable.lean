-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_letwinQuadraticBound_of_tendsto_moments_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.letwinQuadraticBound_of_tendsto_moments_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:24.866563+00:00
-- url     : https://prove2.me/theorems/6ecfa844-3974-41e9-92f3-a8a463c1d859
-- title:
--   Stability of the Quadratic Bound Under Moment Convergence
-- statement:
--   This formalizes the limiting assertion in Lemma A.1 of Letwin (arXiv:2607.24164v1).
--
--   Let $(\mu_k)_{k\in\mathbb N}$ and $\nu$ be probability measures on a finite-dimensional real inner-product space $E$. Assume:
--
--   1. Each identity map belongs to $L^4(\mu_k)$ and to $L^4(\nu)$.
--   2. For every $d\le4$ and every $v:\operatorname{Fin}(d)\to E$, the mixed moments converge:
--      $$\int\prod_i\langle v_i,x\rangle\,d\mu_k(x)\longrightarrow\int\prod_i\langle v_i,x\rangle\,d\nu(x).$$
--   3. Every $\mu_k$ satisfies `LetwinQuadraticBound`.
--
--   Then $\nu$ also satisfies `LetwinQuadraticBound`.
--
--   The result supplies closure of the quadratic-form estimate under convergence of moments through degree four.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem letwinQuadraticBound_of_tendsto_moments [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
--       [BorelSpace E] (μ : ℕ → Measure E) (ν : Measure E) [∀ k, IsProbabilityMeasure (μ k)]
--       [IsProbabilityMeasure ν] (hμ : ∀ k, MemLp id 4 (μ k)) (hν : MemLp id 4 ν)
--       (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
--         Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(μ k)) atTop (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂ν)))
--       (hL : ∀ k, LetwinQuadraticBound (μ k)) : LetwinQuadraticBound ν
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Previous: [`cumulant_map_affine`](https://prove2.me/theorems/ff092742-6b2a-4aa9-b96d-052edb49e94b).
--
--   [Source excerpt, lines 1060–1065](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L1060-L1065) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.1. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L1055-L1131 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.letwinQuadraticBound_of_tendsto_moments`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
universe u
open ProbabilityTheory Filter Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.letwinQuadraticBound_of_tendsto_moments_readable [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : ℕ → Measure E) (ν : Measure E) [∀ k, IsProbabilityMeasure (μ k)]
    [IsProbabilityMeasure ν] (hμ : ∀ k, MemLp id 4 (μ k)) (hν : MemLp id 4 ν)
    (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
      Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(μ k)) atTop (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂ν)))
    (hL : ∀ k, LetwinQuadraticBound (μ k)) : LetwinQuadraticBound ν := by sorry
