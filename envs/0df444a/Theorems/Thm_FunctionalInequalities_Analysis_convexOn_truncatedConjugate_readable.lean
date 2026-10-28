-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_convexOn_truncatedConjugate_readable
-- name    : FunctionalInequalities.Analysis.convexOn_truncatedConjugate_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:52.050234+00:00
-- url     : https://prove2.me/theorems/8b13f81e-b6fb-4053-9362-bcc047017760
-- title:
--   Convexity of the Truncated Conjugate
-- statement:
--   This proves convexity of the truncated conjugate.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $u:E\to\mathbb R$ be continuous. For every $M\ge0$, the function $p\mapsto\operatorname{truncatedConjugate}(u,M,p)$ is convex on all of $E$:
--
--   $$
--   \operatorname{ConvexOn}_{\mathbb R}(E,\operatorname{truncatedConjugate}(u,M)).
--   $$
--
--   The declaration is `convexOn_truncatedConjugate_readable`. The statement concerns the supremum restricted to the closed ball of radius $M$ and makes no claim about strict convexity or differentiability.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem convexOn_truncatedConjugate {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) :
--       ConvexOn ℝ univ (truncatedConjugate u M)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Supporting theorems: [`exists_truncatedConjugate_eq`](https://prove2.me/theorems/c5409e58-60c1-4780-bcb8-119d240430ab).
--
--   Previous: [`exists_truncatedConjugate_eq`](https://prove2.me/theorems/c5409e58-60c1-4780-bcb8-119d240430ab) · Next: [`truncatedConjugate_centered_spec`](https://prove2.me/theorems/e5ce804e-84d7-49ea-8db6-f2b00ef88634).
--
--   [Source excerpt, lines 1309–1310](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1309-L1310) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1308-L1327 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.convexOn_truncatedConjugate`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open Set Metric
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.convexOn_truncatedConjugate_readable {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) :
    ConvexOn ℝ univ (truncatedConjugate u M) := by sorry
