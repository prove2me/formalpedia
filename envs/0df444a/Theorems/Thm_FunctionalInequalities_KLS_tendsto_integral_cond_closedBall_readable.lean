-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_tendsto_integral_cond_closedBall_readable
-- name    : FunctionalInequalities.KLS.tendsto_integral_cond_closedBall_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:25.313523+00:00
-- url     : https://prove2.me/theorems/c2606332-9d4e-4a66-896d-a32140388362
-- title:
--   Convergence of Integrals After Conditioning on a Larger Ball
-- statement:
--   This statement formalizes the conditioning step of Letwin's Lemma A.1.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $(ν_k)$ and $μ$ be probability measures on $E$, with $ν_k\to μ$ in the topology of weak convergence. Let $r<R$, assume that $μ$ gives measure zero to the complement of $\overline B(0,r)$, and let $f:E\to\mathbb R$ be continuous. Then
--
--   $$
--   \int_E f(x)\,d\operatorname{cond}(ν_k,\overline B(0,R))(x)
--   \longrightarrow
--   \int_E f(x)\,dμ(x).
--   $$
--
--   The conclusion concerns the conditional probability measures `ProbabilityTheory.cond` on the closed ball; no boundedness assumption on $f$ is stated.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tendsto_integral_cond_closedBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ℕ → ProbabilityMeasure E}
--       {μ : ProbabilityMeasure E} (hν : Tendsto ν atTop (𝓝 μ)) {r R : ℝ} (hrR : r < R)
--       (hsupp : (μ : Measure E) (closedBall (0 : E) r)ᶜ = 0) {f : E → ℝ} (hf : Continuous f) :
--       Tendsto (fun k => ∫ x, f x ∂(ProbabilityTheory.cond (ν k : Measure E) (closedBall (0 : E) R)))
--         atTop (𝓝 (∫ x, f x ∂(μ : Measure E)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Conditioning`](https://prove2.me/theorems/b0c5089d-02c8-45e7-8c38-91aba9c55475).
--
--   [Source excerpt, lines 372–377](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Conditioning.lean#L372-L377) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Conditioning.lean#L369-L480 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Conditioning`, declaration `FunctionalInequalities.KLS.tendsto_integral_cond_closedBall`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Conditioning

open MeasureTheory Set Metric Filter
open scoped Topology

theorem FunctionalInequalities.KLS.tendsto_integral_cond_closedBall_readable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ℕ → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E} (hν : Tendsto ν atTop (𝓝 μ)) {r R : ℝ} (hrR : r < R)
    (hsupp : (μ : Measure E) (closedBall (0 : E) r)ᶜ = 0) {f : E → ℝ} (hf : Continuous f) :
    Tendsto (fun k => ∫ x, f x ∂(ProbabilityTheory.cond (ν k : Measure E) (closedBall (0 : E) R)))
      atTop (𝓝 (∫ x, f x ∂(μ : Measure E))) := by sorry
