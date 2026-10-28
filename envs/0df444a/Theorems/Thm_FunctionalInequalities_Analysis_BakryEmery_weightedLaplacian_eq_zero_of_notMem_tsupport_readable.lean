-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_weightedLaplacian_eq_zero_of_notMem_tsupport_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_eq_zero_of_notMem_tsupport_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:31.216192+00:00
-- url     : https://prove2.me/theorems/b381f334-820c-4611-a1c1-f11888c8bc19
-- title:
--   Weighted Laplacian Vanishes Outside Closed Support
-- statement:
--   This statement establishes locality of the weighted Laplacian `weightedLaplacian`.
--
--   Let $E$ be a complete finite-dimensional real inner-product space, let $U:E\to\mathbb R$ be arbitrary, let $f:E\to\mathbb R$, and let $x\in E$. If $x$ does not belong to the topological support of $f$, then
--
--   $$
--   \operatorname{weightedLaplacian}(U,f)(x)=0.
--   $$
--
--   The conclusion is independent of the potential $U$ and expresses that the weighted Laplacian vanishes at every point outside the closed support of its argument.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem weightedLaplacian_eq_zero_of_notMem_tsupport (U : E → ℝ) {f : E → ℝ} {x : E}
--       (hx : x ∉ tsupport f) : weightedLaplacian U f x = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   [Source excerpt, lines 51–52](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Laplacian.lean#L51-L52) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Laplacian.lean#L48-L64 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Laplacian`, declaration `FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_eq_zero_of_notMem_tsupport`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Laplacian

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_eq_zero_of_notMem_tsupport_readable (U : E → ℝ) {f : E → ℝ} {x : E}
    (hx : x ∉ tsupport f) : weightedLaplacian U f x = 0 := by sorry
