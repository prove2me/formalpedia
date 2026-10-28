-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_trace_integral_bound_readable
-- name    : FunctionalInequalities.Analysis.trace_integral_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:20.19198+00:00
-- url     : https://prove2.me/theorems/d9cb05da-6288-4525-adcd-78dfcf3313ac
-- title:
--   Trace Integral Bound from Almost-Everywhere Quadratic Expansions
-- statement:
--   This is a technical trace inequality for a convex function with almost-everywhere quadratic expansions.
--
--   Let $u,F,\chi:\mathbb R^n\to\mathbb R$, with $u$ convex and $F$ continuous. Assume that, almost everywhere in $y$, there are a Hermitian positive-definite matrix $B$ and a vector $g$ such that
--
--   1. $F(y)\leq\log\det B$;
--   2. $u$ admits the local quadratic expansion represented by `quadraticAt B y g (u y)` with error at most $\varepsilon\|z-y\|^2$ for every $\varepsilon>0$;
--   3. $\chi$ is $C^2$, compactly supported, and nonnegative.
--
--   Let $H$ be a real matrix satisfying, for every $v\in\mathbb R^n$,
--
--   $$
--   \langle v,Hv\rangle=\int u(y)D^2\chi(y)[v,v] \,dy.
--   $$
--
--   Then every positive-definite matrix $J$ satisfies
--
--   $$
--   \int\bigl(F(y)+\log\det J+n\bigr)\chi(y)\,dy
--   \leq
--   \operatorname{tr}(JH).
--   $$
--
--   The lemma packages the spectral trace comparison needed for the mollified log-determinant estimate.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 800000 in
--   private lemma trace_integral_bound {n : ℕ}
--       {u F χ : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
--       (hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧
--           F y ≤ Real.log B.det ∧ ∃ g : EuclideanSpace ℝ (Fin n),
--             ∀ ε > 0, ∀ᶠ z in 𝓝 y,
--               |u z - quadraticAt B y g (u y) z| ≤ ε * ‖z - y‖ ^ 2)
--       (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ y, 0 ≤ χ y)
--       (H : Matrix (Fin n) (Fin n) ℝ)
--       (hH : ∀ v : EuclideanSpace ℝ (Fin n),
--         ⟪v, Matrix.toEuclideanLin H v⟫ =
--           ∫ y, u y * iteratedFDeriv ℝ 2 χ y (fun _ => v))
--       (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.PosDef) :
--       (∫ y, (F y + Real.log J.det + n) * χ y) ≤ (J * H).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Supporting theorems: [`forall_posDef_add_log_det_le_trace_iff`](https://prove2.me/theorems/99f67c0b-fea3-4671-8e5b-e62a896aa733), [`integral_mul_le_integral_mul_sum_iteratedFDeriv`](https://prove2.me/theorems/a34ffeae-071d-4fec-b551-07733fa204a2), [`expansion_secondDifference`](https://prove2.me/theorems/546aab2f-04b5-4802-87d1-3ee07a4c5efe).
--
--   Previous: [`convolution_hessian_integral`](https://prove2.me/theorems/71cd5614-d749-4ac1-8ee0-bcd17a10ea5c) · Next: [`posDef_and_convolution_le_log_det_hessianMatrix`](https://prove2.me/theorems/6d69beca-a1f9-48e2-959c-68716a21a551).
--
--   [Source excerpt, lines 1254–1269](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1254-L1269) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1254-L1320 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `_private.FunctionalInequalities.Analysis.Convex.Viscosity.0.FunctionalInequalities.Analysis.trace_integral_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
set_option maxHeartbeats 800000

lemma FunctionalInequalities.Analysis.trace_integral_bound_readable {n : ℕ}
    {u F χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
    (hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧
        F y ≤ Real.log B.det ∧ ∃ g : EuclideanSpace ℝ (Fin n),
          ∀ ε > 0, ∀ᶠ z in 𝓝 y,
            |u z - quadraticAt B y g (u y) z| ≤ ε * ‖z - y‖ ^ 2)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ y, 0 ≤ χ y)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, Matrix.toEuclideanLin H v⟫ =
        ∫ y, u y * iteratedFDeriv ℝ 2 χ y (fun _ => v))
    (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.PosDef) :
    (∫ y, (F y + Real.log J.det + n) * χ y) ≤ (J * H).trace := by sorry
