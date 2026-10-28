-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_sum_variance_entries_eq_integral_trace_sub_trace_mean_readable
-- name    : FunctionalInequalities.Probability.sum_variance_entries_eq_integral_trace_sub_trace_mean_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:17.723863+00:00
-- url     : https://prove2.me/theorems/88527e56-76ae-4a12-8518-4edc0d238008
-- title:
--   Sum of Matrix Entry Variances as a Trace Difference
-- statement:
--   This is a finite-dimensional random-matrix variance identity.
--
--   Let $\mu$ be a probability measure on a measurable space $\alpha$. Let $H:\alpha\to\mathbb R^{n\times n}$ be almost-everywhere symmetric, with every entry in $L^2(\mu)$, and let $M\in\mathbb R^{n\times n}$ be symmetric. Assume that $M_{ij}=\int H_{ij}(x)\,d\mu(x)$ for every $i,j$. Then
--
--   $$\sum_{i,j}\operatorname{Var}_{\mu}(H_{ij})
--   =\int_\alpha\operatorname{tr}\!\bigl(H(x)H(x)\bigr)\,d\mu(x)-\operatorname{tr}(M^2).$$
--
--   This identity converts entrywise variance sums into trace expressions and is reusable in Hessian and matrix-energy estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_variance_entries_eq_integral_trace_sub_trace_mean {alpha : Type*} [MeasurableSpace alpha]
--       {n : ℕ} (mu : Measure alpha) [IsProbabilityMeasure mu]
--       (H : alpha → Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
--       (hM : M.IsSymm) (hH : ∀ᵐ x ∂mu, (H x).IsSymm)
--       (hH2 : ∀ i j, MemLp (fun x => H x i j) 2 mu)
--       (hmean : ∀ i j, (∫ x, H x i j ∂mu) = M i j) :
--       (∑ p : Fin n × Fin n, ProbabilityTheory.variance (fun x => H x p.1 p.2) mu) =
--         (∫ x, (H x * H x).trace ∂mu) - (M * M).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Moments`](https://prove2.me/theorems/b17c0176-d838-4b45-bc76-c9e62313e1ce).
--
--   Supporting theorems: [`sum_matrix_product_entry_mul_eq_trace`](https://prove2.me/theorems/3c931abe-bff8-4022-a4df-7236818e79cd).
--
--   Next: [`memLp_quadratic_of_memLp_four`](https://prove2.me/theorems/80afcd22-0f06-48b5-88c9-0fb875897eef).
--
--   [Source excerpt, lines 469–476](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Moments.lean#L469-L476) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Moments.lean#L467-L493 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Moments`, declaration `FunctionalInequalities.Probability.sum_variance_entries_eq_integral_trace_sub_trace_mean`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Moments

open MeasureTheory Matrix

theorem FunctionalInequalities.Probability.sum_variance_entries_eq_integral_trace_sub_trace_mean_readable {alpha : Type*} [MeasurableSpace alpha]
    {n : ℕ} (mu : Measure alpha) [IsProbabilityMeasure mu]
    (H : alpha → Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (hH : ∀ᵐ x ∂mu, (H x).IsSymm)
    (hH2 : ∀ i j, MemLp (fun x => H x i j) 2 mu)
    (hmean : ∀ i j, (∫ x, H x i j ∂mu) = M i j) :
    (∑ p : Fin n × Fin n, ProbabilityTheory.variance (fun x => H x p.1 p.2) mu) =
      (∫ x, (H x * H x).trace ∂mu) - (M * M).trace := by sorry
