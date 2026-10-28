-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_exists_graph_norm_moment_of_local_moments_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.exists_graph_norm_moment_of_local_moments_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:05.605717+00:00
-- url     : https://prove2.me/theorems/8a8ce263-41ce-4c1c-a341-699721b9b1dc
-- title:
--   Existence of a Graph-Law Exponential Norm Moment
-- statement:
--   This lemma states existence of an exponential norm moment for the graph law from two separate exponential-moment assumptions.
--
--   Let $n\in\mathbb N$, $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), $\mu$ a probability measure on $E$, and $f:E\to\mathbb R$ measurable. Let $a,s>0$ and assume
--   1. $x\mapsto e^{a|f(x)|}\in L^1(\mu)$.
--   2. $x\mapsto e^{s\|x\|}\in L^1(\mu)$.
--
--   Let $G:E\to\mathbb R^{\operatorname{Option}(\operatorname{Fin}n)}$ be the Euclidean graph map with $G(x)_{\mathrm{none}}=f(x)$ and $G(x)_{\mathrm{some}(j)}=x_j$, and let $\Gamma=G_*\mu$ (`Measure.map`). Then
--   $$
--   \exists t\in\mathbb R,\quad t>0\ \text{and}\ y\mapsto e^{t\|y\|}\in L^1(\Gamma).
--   $$
--
--   This provides a local norm-moment condition on the joint vector $(f(x),x)$ for subsequent transform calculations. Only existence of a positive rate is asserted.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_graph_norm_moment_of_local_moments {n : ℕ}
--       (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
--       {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
--       {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
--       (hfa : Integrable (fun x => Real.exp (a * |f x|)) μ)
--       (hxs : Integrable (fun x => Real.exp (s * ‖x‖)) μ) :
--       ∃ t : ℝ, 0 < t ∧
--         Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))
--           (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
--             (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
--               EuclideanSpace ℝ (Option (Fin n)))))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Cumulant`](https://prove2.me/theorems/01ff1334-f332-41dc-ab58-0fb2ead9dd7b).
--
--   Previous: [`exists_f_abs_exponential_moment`](https://prove2.me/theorems/fe683760-0019-4c41-91b0-97d1cf8c50c3).
--
--   [Source excerpt, lines 362–372](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean#L362-L372) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean#L360-L435 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Cumulant`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.exists_graph_norm_moment_of_local_moments`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor

theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_graph_norm_moment_of_local_moments_readable {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hfa : Integrable (fun x => Real.exp (a * |f x|)) μ)
    (hxs : Integrable (fun x => Real.exp (s * ‖x‖)) μ) :
    ∃ t : ℝ, 0 < t ∧
      Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))
        (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
            EuclideanSpace ℝ (Option (Fin n))))) := by sorry
