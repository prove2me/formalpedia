-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_pos_volume_convexHull_closedBall_union_singleton_ge_readable
-- name    : FunctionalInequalities.Analysis.exists_pos_volume_convexHull_closedBall_union_singleton_ge_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:50.488587+00:00
-- url     : https://prove2.me/theorems/04941f10-f990-4b5d-a225-77ccc909d39f
-- title:
--   Volume Lower Bound for a Ball Cone
-- statement:
--   This gives the volume lower bound for the convex hull of a ball and an exterior point.
--
--   Let $E$ be a finite-dimensional real inner-product space with its measurable and Borel structures, and write $n=\dim E$. There exists $c>0$, depending only on $E$, such that for every $r>0$ and every $q\in E$ with $r\le\|q\|$,
--
--   $$
--   \operatorname{ofReal}\!\left(c\,r^{n-1}\|q\|\right)
--   \le
--   \operatorname{vol}\!\left(\operatorname{convHull}\left(\overline B(0,r)\cup\{q\}\right)\right).
--   $$
--
--   The volume values are in $[0,\infty]$ (`ENNReal`), and the real expression is embedded using `ofReal`. The declaration is `exists_pos_volume_convexHull_closedBall_union_singleton_ge_readable`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_pos_volume_convexHull_closedBall_union_singleton_ge {E : Type*}
--       [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
--       [BorelSpace E] :
--       ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → ∀ q : E, r ≤ ‖q‖ →
--         ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
--           (volume : Measure E) (convexHull ℝ (closedBall (0 : E) r ∪ {q}))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Previous: [`exists_unit_inner_le_infDist_frontier`](https://prove2.me/theorems/f4f9ef6d-abf7-4073-89c1-856846d679e9) · Next: [`exists_pos_alexandrov_maximum_principle`](https://prove2.me/theorems/fb6f8a3c-985d-4638-9d88-5993fe585328).
--
--   [Source excerpt, lines 749–754](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L749-L754) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L746-L1054 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.exists_pos_volume_convexHull_closedBall_union_singleton_ge`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

open MeasureTheory Set Metric

theorem FunctionalInequalities.Analysis.exists_pos_volume_convexHull_closedBall_union_singleton_ge_readable {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → ∀ q : E, r ≤ ‖q‖ →
      ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
        (volume : Measure E) (convexHull ℝ (closedBall (0 : E) r ∪ {q})) := by sorry
