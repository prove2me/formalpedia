-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_expansion_secondDifference_readable
-- name    : FunctionalInequalities.Analysis.expansion_secondDifference_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:04.212646+00:00
-- url     : https://prove2.me/theorems/546aab2f-04b5-4802-87d1-3ee07a4c5efe
-- title:
--   Second Difference Expansion Along a Direction
-- statement:
--   This is a technical one-dimensional second-difference lemma for a quadratic second-order expansion.
--
--   Let $n\in\mathbb N$, let $u:\mathbb R^n\to\mathbb R$, let $x,v,g\in\mathbb R^n$, and let $B$ be a real $n\times n$ matrix, with the space represented by `EuclideanSpace ℝ (Fin n)`. Assume that for every $\varepsilon>0$, the function $u$ satisfies near $x$
--
--   $$
--   \left|u(y)-Q_{B,x,g,u(x)}(y)\right|\leq \varepsilon\|y-x\|^2
--   $$
--
--   for almost every $y$ in some neighborhood of $x$, where `quadraticAt` is the quadratic test function used in the formalization. Then, as $t\to0$ through positive real values,
--
--   $$
--   \frac{u(x+tv)+u(x-tv)-2u(x)}{t^2}\longrightarrow \langle v,Bv\rangle.
--   $$
--
--   This auxiliary result extracts the quadratic coefficient from a viscosity-style second-order expansion and is reusable whenever such expansions are available.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma expansion_secondDifference {n : ℕ}
--       {u : EuclideanSpace ℝ (Fin n) → ℝ} {x g : EuclideanSpace ℝ (Fin n)}
--       {B : Matrix (Fin n) (Fin n) ℝ}
--       (h : ∀ ε > 0, ∀ᶠ y in 𝓝 x,
--         |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2)
--       (v : EuclideanSpace ℝ (Fin n)) :
--       Tendsto (fun t : ℝ =>
--         (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2)
--         (𝓝[>] 0) (𝓝 ⟪v, Matrix.toEuclideanLin B v⟫)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Previous: [`posDef_and_det_eq_of_quadratic_expansion`](https://prove2.me/theorems/fdeb8c35-d7cf-4a28-9642-da29fd09799b) · Next: [`convolution_hessian_integral`](https://prove2.me/theorems/71cd5614-d749-4ac1-8ee0-bcd17a10ea5c).
--
--   [Source excerpt, lines 992–1000](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L992-L1000) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L992-L1062 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `_private.FunctionalInequalities.Analysis.Convex.Viscosity.0.FunctionalInequalities.Analysis.expansion_secondDifference`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology

lemma FunctionalInequalities.Analysis.expansion_secondDifference_readable {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x g : EuclideanSpace ℝ (Fin n)}
    {B : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ ε > 0, ∀ᶠ y in 𝓝 x,
      |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ =>
      (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2)
      (𝓝[>] 0) (𝓝 ⟪v, Matrix.toEuclideanLin B v⟫) := by sorry
