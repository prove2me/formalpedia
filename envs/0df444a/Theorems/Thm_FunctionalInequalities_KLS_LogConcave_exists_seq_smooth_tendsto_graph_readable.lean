-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_graph_readable
-- name    : FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_graph_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:06.32301+00:00
-- url     : https://prove2.me/theorems/c7be6850-4704-4912-95fa-1692fa90fd5a
-- title:
--   Smooth Compactly Supported Graph-Norm Core
-- statement:
--   This theorem gives a sequential graph-norm core for the closed weighted-gradient operator.
--
--   Let $V$ be a finite-dimensional real inner-product space with the stated measurable, Borel, complete, and second-countable structures. Let $m$ be an additive Haar measure on $V$, let $\nu$ be a log-concave probability measure, let $B:V\to V$ be continuous linear, and assume that the interior of the support of $\nu$ is nonempty. For any
--
--   $$
--   x\in D\!\left(\overline{T}_{\nu,m,B}\right),
--   $$
--
--   there exist functions $g_n:V\to\mathbb R$ such that each $g_n$ is $C^\infty$ and compactly supported, and
--
--   $$
--   [g_n]\longrightarrow x \quad\text{in }L^2(\nu),
--   $$
--
--   while
--
--   $$
--   [B\nabla g_n]\longrightarrow \overline{T}_{\nu,m,B}x
--   \quad\text{in }L^2(\nu;V).
--   $$
--
--   In Lean, the operator is `closedWeightedOperator`, and the convergences are expressed using `MemLp.toLp` and `Tendsto`. The result controls the function and its first weighted derivative only; it makes no assertion about second-order quantities.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_seq_smooth_tendsto_graph (x : (hν.closedWeightedOperator m B hi).domain) :
--       ∃ (g : ℕ → V → ℝ) (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hgc : ∀ n, HasCompactSupport (g n)),
--         Tendsto (fun n => (memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n))
--             atTop (𝓝 (x : Lp ℝ 2 (ν : Measure V))) ∧
--           Tendsto (fun n => (IsTest.of_contDiff_hasCompactSupport ν B (hg n)
--               (hgc n)).memLp_apply.toLp (apply B (g n))) atTop
--             (𝓝 (hν.closedWeightedOperator m B hi x))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeightedGradient/Multiplier`](https://prove2.me/theorems/5b6390bb-3865-4ef0-88d2-fa41db26a901).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Energy/WeightedGradient/Basic`](https://prove2.me/theorems/f6b93e94-4e8d-4cc9-94ea-458e2669b85c), [`Energy/WeightedGradient/Core`](https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f).
--
--   Next: [`exists_mem_domain_closedWeightedOperator_toLp_mul`](https://prove2.me/theorems/465ec746-a212-4a4a-a2ab-2d9cca0a20ec).
--
--   [Source excerpt, lines 55–61](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Multiplier.lean#L55-L61) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Multiplier.lean#L50-L104 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Multiplier`, declaration `FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_graph`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier

open MeasureTheory Filter Topology
open scoped ContDiff
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient FunctionalInequalities.Analysis.Semigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)

theorem FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_graph_readable (x : (hν.closedWeightedOperator m B hi).domain) :
    ∃ (g : ℕ → V → ℝ) (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hgc : ∀ n, HasCompactSupport (g n)),
      Tendsto (fun n => (memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n))
          atTop (𝓝 (x : Lp ℝ 2 (ν : Measure V))) ∧
        Tendsto (fun n => (IsTest.of_contDiff_hasCompactSupport ν B (hg n)
            (hgc n)).memLp_apply.toLp (apply B (g n))) atTop
          (𝓝 (hν.closedWeightedOperator m B hi x)) := by sorry
