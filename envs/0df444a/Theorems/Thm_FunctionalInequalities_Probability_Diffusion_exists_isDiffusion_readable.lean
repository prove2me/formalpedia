-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_exists_isDiffusion_readable
-- name    : FunctionalInequalities.Probability.Diffusion.exists_isDiffusion_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:36.61219+00:00
-- url     : https://prove2.me/theorems/7af98979-05ab-4014-86ce-c2315b88e573
-- title:
--   Existence Of A Globally Lipschitz Bounded Diffusion
-- statement:
--   This theorem establishes existence of a diffusion on a Brownian filtered probability space. Let $(\Omega,P)$ be a probability space, let $W$ be a $d$-dimensional Brownian motion, and let $\mathcal F$ be a right-continuous filtration making each coordinate Brownian. Assume the filtration ordering and null-set hypotheses in the statement. Let
--
--   $$b:\mathbb R^N\to\mathbb R^N,\qquad \sigma:\mathbb R^N\to(\mathbb R^d\to\mathbb R^N),$$
--
--   and let $K\in[0,\infty)$ be an `NNReal`. Suppose $b$ and every $x\mapsto\sigma(x,k)$ are $K$-Lipschitz. Suppose also that for some $B\in\mathbb R$,
--
--   $$\|b(x)\|\leq B,\qquad \|\sigma(x,k)\|\leq B$$
--
--   for all $x$ and $k$. Then for every initial state $x_0\in\mathbb R^N$ there exists a path map $Y:\mathbb R\to\Omega\to\mathbb R^N$ such that `IsDiffusion W ℱ hW b σ x₀ Y` holds. The bundled predicate supplies the diffusion's measurability, adaptedness, continuity, and Itô representation properties.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Diffusion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_isDiffusion (W : MultidimBrownianMotion P d)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
--       (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {K : ℝ≥0}
--       (hb : LipschitzWith K b) (hσ : ∀ k, LipschitzWith K fun x => σ x k)
--       {B : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B) (hσB : ∀ x k, ‖σ x k‖ ≤ B) (x₀ : Fin N → ℝ) :
--       ∃ Y : ℝ → Ω → Fin N → ℝ, IsDiffusion W ℱ hW b σ x₀ Y
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Diffusion/Existence`](https://prove2.me/theorems/523c289a-088b-456f-9966-2cf2f32eb8dc).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`Probability/Diffusion/Setup`](https://prove2.me/theorems/75711a6c-6c0c-4b07-ab17-35ac267ca6bd).
--
--   Supporting theorems: [`exists_isVectorItoVersion_of_unbounded`](https://prove2.me/theorems/31d4b1e5-43c0-487e-8cd2-7922775543cc), [`vectorItoProcess_ae_eq_zero`](https://prove2.me/theorems/2c299ed7-02cc-4215-b871-f99239baed20), [`exists_globalSolution`](https://prove2.me/theorems/90eec698-1731-47a5-9f64-89ce1ff7ee42), [`itoIntegral_congr_ae`](https://prove2.me/theorems/5b2a8fe4-013f-4df7-9936-5da724b67c11), [`diffusionCoeffs_lipschitz`](https://prove2.me/theorems/fd8b709d-67fc-4441-99f2-2be39c9c9a73).
--
--   Previous: [`diffusionCoeffs_lipschitz`](https://prove2.me/theorems/fd8b709d-67fc-4441-99f2-2be39c9c9a73).
--
--   [Source excerpt, lines 164–172](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Existence.lean#L164-L172) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Existence.lean#L161-L302 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Existence`, declaration `FunctionalInequalities.Probability.Diffusion.exists_isDiffusion`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Existence

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito
variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure P] {N d : ℕ}
open LevyStochCalc.Ito.Picard

theorem FunctionalInequalities.Probability.Diffusion.exists_isDiffusion_readable (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {K : ℝ≥0}
    (hb : LipschitzWith K b) (hσ : ∀ k, LipschitzWith K fun x => σ x k)
    {B : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B) (hσB : ∀ x k, ‖σ x k‖ ≤ B) (x₀ : Fin N → ℝ) :
    ∃ Y : ℝ → Ω → Fin N → ℝ, IsDiffusion W ℱ hW b σ x₀ Y := by sorry
