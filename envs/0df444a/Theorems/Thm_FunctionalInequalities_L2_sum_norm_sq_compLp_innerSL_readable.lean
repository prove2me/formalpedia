-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_sum_norm_sq_compLp_innerSL_readable
-- name    : FunctionalInequalities.L2.sum_norm_sq_compLp_innerSL_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:58.038127+00:00
-- url     : https://prove2.me/theorems/886e463b-28f3-4769-9471-649161462a00
-- title:
--   Parseval Identity for Vector-Valued $L^2$ Components
-- statement:
--   This statement gives Parseval's identity in vector-valued $L^2$.
--
--   Let $(\alpha,\mu)$ be a measurable space with measure $\mu$, let $G$ be a real inner-product normed space, let $\iota$ be a finite index type, and let $b=(b_k)_{k\in\iota}$ be an orthonormal basis of $G$. For any $g\in L^2(\mu;G)$, take the scalar component $(x\mapsto\langle b_k,g(x)\rangle)$ for each basis vector. Then
--
--   $$\sum_{k\in\iota}\left\|\langle b_k,\,g(\cdot)\rangle\right\|_{L^2(\mu)}^2=\|g\|_{L^2(\mu;G)}^2.$$
--
--   This is the componentwise identity used to transfer scalar estimates to finite-dimensional vector-valued data.
--
--   **Formalization Note:** The components are represented by `(innerSL ℝ (b k)).compLp g`; the equality is in real $L^2$ and requires only a measurable space for the underlying measure.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.L2`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_norm_sq_compLp_innerSL {μ : Measure α} {ι : Type*} [Fintype ι]
--       (b : OrthonormalBasis ι ℝ G) (g : Lp G 2 μ) :
--       ∑ k, ‖(innerSL ℝ (b k)).compLp g‖ ^ 2 = ‖g‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`L2/Components`](https://prove2.me/theorems/65f234d7-c15f-4bd7-83af-57581900820d).
--
--   [Source excerpt, lines 60–62](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/Components.lean#L60-L62) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/Components.lean#L58-L74 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.Components`, declaration `FunctionalInequalities.L2.sum_norm_sq_compLp_innerSL`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_Components

open MeasureTheory
variable {α : Type*} [MeasurableSpace α]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem FunctionalInequalities.L2.sum_norm_sq_compLp_innerSL_readable {μ : Measure α} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ G) (g : Lp G 2 μ) :
    ∑ k, ‖(innerSL ℝ (b k)).compLp g‖ ^ 2 = ‖g‖ ^ 2 := by sorry
