-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_exists_f_abs_exponential_moment_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.exists_f_abs_exponential_moment_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:02.18373+00:00
-- url     : https://prove2.me/theorems/fe683760-0019-4c41-91b0-97d1cf8c50c3
-- title:
--   Existence of an Absolute Exponential Moment From the Joint Law
-- statement:
--   This lemma transfers existence of an exponential norm moment of the suspension joint law to an absolute exponential moment of the observable.
--
--   Let $n,N\in\mathbb N$ with $N>0$, let $\mu$ be a probability measure on $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), and let $f:E\to\mathbb R$ be measurable. Let $\beta,r>0$, $\sigma_\beta=\sqrt{1+2/\beta^2}$ (`sigma`), and $\lambda=$ `jointLaw` $\mu\ f\ \beta\ \sigma_\beta\ N$. This is the law on `JointSpace` $N\ n$ of the scalar $(N^{-1/2}\sum_i f(X_i)+\eta)/\sigma_\beta$ and the copies, with independent Laplace noise $\eta$ of rate $\beta$.
--
--   Assume $p\mapsto e^{r\|p\|}$ is integrable under $\lambda$. Then
--   $$
--   \exists t\in\mathbb R,\quad t>0\ \text{and}\ x\mapsto e^{t|f(x)|}\in L^1(\mu).
--   $$
--
--   This is an existence result for a positive rate, useful for local transform regularity. Its conclusion does not prescribe a particular value of $t$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_f_abs_exponential_moment {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
--       [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
--       {β r : ℝ} (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
--       (hexp : Integrable (fun p : JointSpace N n => Real.exp (r * ‖p‖))
--         (jointLaw μ f β (sigma β) N)) :
--       ∃ t : ℝ, 0 < t ∧ Integrable (fun x => Real.exp (t * |f x|)) μ
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Cumulant`](https://prove2.me/theorems/01ff1334-f332-41dc-ab58-0fb2ead9dd7b).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3).
--
--   Supporting theorems: [`joint_integrability_factorization`](https://prove2.me/theorems/62722319-aff7-42a5-ab4b-17e27bbeed8e).
--
--   Previous: [`logLaplace_jointLaw_factorization`](https://prove2.me/theorems/d7decbed-2d29-44e0-9116-1fd9deec5adb) · Next: [`exists_graph_norm_moment_of_local_moments`](https://prove2.me/theorems/8a8ce263-41ce-4c1c-a341-699721b9b1dc).
--
--   [Source excerpt, lines 303–308](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean#L303-L308) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean#L300-L358 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Cumulant`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.exists_f_abs_exponential_moment`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor

theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_f_abs_exponential_moment_readable {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r : ℝ} (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hexp : Integrable (fun p : JointSpace N n => Real.exp (r * ‖p‖))
      (jointLaw μ f β (sigma β) N)) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun x => Real.exp (t * |f x|)) μ := by sorry
