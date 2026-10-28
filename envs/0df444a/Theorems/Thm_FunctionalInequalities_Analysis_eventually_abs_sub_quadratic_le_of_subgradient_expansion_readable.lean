-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_eventually_abs_sub_quadratic_le_of_subgradient_expansion_readable
-- name    : FunctionalInequalities.Analysis.eventually_abs_sub_quadratic_le_of_subgradient_expansion_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:13.940581+00:00
-- url     : https://prove2.me/theorems/4ddfd262-d82d-4fdf-95dc-67ccaaffbd1b
-- title:
--   Subgradient Expansion Implies Quadratic Function Expansion
-- statement:
--   This is an auxiliary second-order expansion lemma for convex functions.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $f:E\to\mathbb R$ be convex on $E$, let $x,p\in E$, and let $B:E\to E$ be continuous linear. Assume that for every $\varepsilon>0$, for all $y$ sufficiently near $x$, every subgradient $q$ of $f$ at $y$ satisfies
--
--   $$\|q-p-B(y-x)\|\le \varepsilon\|y-x\|.$$
--
--   Then, for every $\varepsilon>0$, for all $y$ sufficiently near $x$,
--
--   $$\left|f(y)-f(x)-\langle p,y-x\rangle-\frac12\langle B(y-x),y-x\rangle\right|\le \varepsilon\|y-x\|^2.$$
--
--   The declaration `eventually_abs_sub_quadratic_le_of_subgradient_expansion_readable` converts a first-order local estimate on all subgradients into a second-order local estimate for the function. The same symbol $\varepsilon$ is used in both quantified conclusions, exactly as in the Lean statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem eventually_abs_sub_quadratic_le_of_subgradient_expansion [FiniteDimensional ℝ E] {f : E → ℝ}
--       (hconv : ConvexOn ℝ univ f) {x p : E} {B : E →L[ℝ] E}
--       (hexp : ∀ ε > 0, ∀ᶠ y in 𝓝 x, ∀ q : E, (∀ w, f y + ⟪q, w - y⟫ ≤ f w) →
--         ‖q - p - B (y - x)‖ ≤ ε * ‖y - x‖) :
--       ∀ ε > 0, ∀ᶠ y in 𝓝 x,
--         |f y - f x - ⟪p, y - x⟫ - (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`exists_subgradient_slope_le_inner_add`](https://prove2.me/theorems/030b4fd7-878c-4020-bf9d-be7e6b77019e).
--
--   Previous: [`volume_subgradient_two_points_eq_zero`](https://prove2.me/theorems/097fae72-0e02-4d52-bbb1-f4883ba49bd8).
--
--   [Source excerpt, lines 1439–1444](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L1439-L1444) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L1434-L1543 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.eventually_abs_sub_quadratic_le_of_subgradient_expansion`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient

open Set Filter
open scoped RealInnerProductSpace Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.eventually_abs_sub_quadratic_le_of_subgradient_expansion_readable [FiniteDimensional ℝ E] {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) {x p : E} {B : E →L[ℝ] E}
    (hexp : ∀ ε > 0, ∀ᶠ y in 𝓝 x, ∀ q : E, (∀ w, f y + ⟪q, w - y⟫ ≤ f w) →
      ‖q - p - B (y - x)‖ ≤ ε * ‖y - x‖) :
    ∀ ε > 0, ∀ᶠ y in 𝓝 x,
      |f y - f x - ⟪p, y - x⟫ - (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by sorry
