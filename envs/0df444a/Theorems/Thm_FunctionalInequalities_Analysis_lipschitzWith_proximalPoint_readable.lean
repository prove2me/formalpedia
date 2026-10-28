-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_lipschitzWith_proximalPoint_readable
-- name    : FunctionalInequalities.Analysis.lipschitzWith_proximalPoint_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:16.961611+00:00
-- url     : https://prove2.me/theorems/400fd9e1-fb0c-4e87-8ab5-d48890ee12a0
-- title:
--   The Proximal Map Is One-Lipschitz
-- statement:
--   This formalizes the nonexpansiveness property of the proximal map.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $f:E\to\mathbb R$ be convex on all of $E$. For the Lean definition `proximalPoint f`, the map is $1$-Lipschitz:
--
--   $$\|\operatorname{prox}_f(z)-\operatorname{prox}_f(w)\|\le \|z-w\|\qquad(z,w\in E).$$
--
--   Equivalently, `proximalPoint f` is `LipschitzWith 1`. This declaration supplies a global continuity estimate used by later almost-everywhere differentiability arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lipschitzWith_proximalPoint {f : E → ℝ} (hconv : ConvexOn ℝ univ f) :
--       LipschitzWith 1 (proximalPoint f)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Proximal`](https://prove2.me/theorems/1d665bc1-5792-4d08-9238-1bf12adef58c).
--
--   Supporting theorems: [`exists_subgradient_slope_le_inner_add`](https://prove2.me/theorems/030b4fd7-878c-4020-bf9d-be7e6b77019e).
--
--   Next: [`hasFDerivAt_half_sq_sub_moreau`](https://prove2.me/theorems/746705d4-4726-407e-8f1b-f9fdde75a858).
--
--   [Source excerpt, lines 162–163](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean#L162-L163) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean#L161-L178 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Proximal`, declaration `FunctionalInequalities.Analysis.lipschitzWith_proximalPoint`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Proximal

open Set
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.lipschitzWith_proximalPoint_readable {f : E → ℝ} (hconv : ConvexOn ℝ univ f) :
    LipschitzWith 1 (proximalPoint f) := by sorry
