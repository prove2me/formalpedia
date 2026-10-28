-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_posDef_and_convolution_le_log_det_hessianMatrix_readable
-- name    : FunctionalInequalities.Analysis.posDef_and_convolution_le_log_det_hessianMatrix_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:22.633065+00:00
-- url     : https://prove2.me/theorems/6d69beca-a1f9-48e2-959c-68716a21a551
-- title:
--   Mollified Log-Determinant Lower Bound
-- statement:
--   This is the mollified log-det lower bound from the weak Letwin route.
--
--   Let $u,F:\mathbb R^n\to\mathbb R$, with $u$ convex and $F$ continuous. Assume that, almost everywhere in $x$, there exist a Hermitian positive-definite matrix $B$ and a vector $g$ such that
--
--   1. $F(x)\leq\log\det B$;
--   2. for every $\varepsilon>0$, $u$ has at $x$ the quadratic expansion represented by `quadraticAt B x g (u x)`, with error bounded by $\varepsilon\|y-x\|^2$ near $x$.
--
--   For every $C^2$ compactly supported bump $\phi$ normalized with respect to volume, and every $x\in\mathbb R^n$, the convolution $u_\phi=\phi.\mathrm{normed}*u$ has positive-definite Hessian and
--
--   $$
--   (\phi.\mathrm{normed}*F)(x)
--   \leq
--   \log\det\nabla^2u_\phi(x).
--   $$
--
--   This is the formalized mollified determinant inequality and can be reused as the regularized convexity input in moment-map arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem posDef_and_convolution_le_log_det_hessianMatrix {n : ℕ}
--       {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
--       (hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧ F x ≤ Real.log B.det ∧
--           ∃ g : EuclideanSpace ℝ (Fin n),
--             ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2)
--       (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
--       (hessianMatrix (convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x).PosDef ∧
--         convolution (φ.normed volume) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x ≤
--           Real.log (hessianMatrix
--             (convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x).det
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Supporting theorems: [`forall_posDef_add_log_det_le_trace_iff`](https://prove2.me/theorems/99f67c0b-fea3-4671-8e5b-e62a896aa733), [`posSemidef_hessianMatrix_of_upper_touch`](https://prove2.me/theorems/c0934c18-f16d-42fc-a97b-28fa4ccb6c6d), [`convolution_hessian_integral`](https://prove2.me/theorems/71cd5614-d749-4ac1-8ee0-bcd17a10ea5c), [`trace_integral_bound`](https://prove2.me/theorems/d9cb05da-6288-4525-adcd-78dfcf3313ac).
--
--   Previous: [`trace_integral_bound`](https://prove2.me/theorems/d9cb05da-6288-4525-adcd-78dfcf3313ac) · Next: [`ae_exists_quadraticAt_expansion`](https://prove2.me/theorems/995efd14-b691-40e5-adc5-c0effdf385d3).
--
--   [Source excerpt, lines 1327–1337](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1327-L1337) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1322-L1393 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `FunctionalInequalities.Analysis.posDef_and_convolution_le_log_det_hessianMatrix`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open FunctionalInequalities.Probability.Stein
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology

theorem FunctionalInequalities.Analysis.posDef_and_convolution_le_log_det_hessianMatrix_readable {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
    (hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧ F x ≤ Real.log B.det ∧
        ∃ g : EuclideanSpace ℝ (Fin n),
          ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    (hessianMatrix (convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x).PosDef ∧
      convolution (φ.normed volume) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x ≤
        Real.log (hessianMatrix
          (convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x).det := by sorry
