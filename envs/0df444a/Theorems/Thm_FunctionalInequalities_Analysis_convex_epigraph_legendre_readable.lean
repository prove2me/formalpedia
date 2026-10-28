-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_legendre_readable
-- name    : FunctionalInequalities.Analysis.convex_epigraph_legendre_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:47.629156+00:00
-- url     : https://prove2.me/theorems/ae6b66c7-c45b-4b02-ba8a-8dcdbef9e183
-- title:
--   Convexity of the Real Legendre Epigraph
-- statement:
--   This proves convexity of the real epigraph of the Legendre transform.
--
--   Let $E$ be a real inner-product space and let $\varphi:E\to\overline{\mathbb R}$ be arbitrary, with `EReal` allowing the values $\pm\infty$. Define the Legendre transform by `legendre`. Then
--   $$\left\{(p,r)\in E\times\mathbb R:\operatorname{legendre}(\varphi)(p)\le r\right\}$$
--   is convex.
--
--   The statement is measure-free and applies without convexity, properness, or finiteness assumptions on $\varphi$. It is basic infrastructure for later properties of conjugates and biconjugates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem convex_epigraph_legendre (φ : E → EReal) :
--       Convex ℝ {p : E × ℝ | legendre φ p.1 ≤ (p.2 : EReal)}
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Next: [`legendre_ne_bot_iff`](https://prove2.me/theorems/9d709974-65b3-421f-a939-a9573b181df1).
--
--   [Source excerpt, lines 151–152](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L151-L152) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L149-L178 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Legendre`, declaration `FunctionalInequalities.Analysis.convex_epigraph_legendre`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.convex_epigraph_legendre_readable (φ : E → EReal) :
    Convex ℝ {p : E × ℝ | legendre φ p.1 ≤ (p.2 : EReal)} := by sorry
