-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_affineSubtract_readable
-- name    : FunctionalInequalities.Analysis.convex_epigraph_affineSubtract_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:56.757765+00:00
-- url     : https://prove2.me/theorems/ddb03546-bc6f-456e-b9a9-168872a634c9
-- title:
--   Affine Subtraction Preserves Epigraph Convexity
-- statement:
--   This proves preservation of real epigraph convexity under affine subtraction.
--
--   Let $E$ be a real inner-product space, let $f:E\to\overline{\mathbb R}$, let $a\in E$, and let $b\in\mathbb R$. Assume the real epigraph
--   $$\{(p,r)\in E\times\mathbb R:f(p)\le r\}$$
--   is convex. Define `affineSubtract` by
--   $$\operatorname{affineSubtract}(f,a,b)(x)=f(x)-\bigl(\langle a,x\rangle+b\bigr).$$
--   Then its real epigraph is convex:
--   $$\{(p,r):\operatorname{affineSubtract}(f,a,b)(p)\le r\}\text{ is convex}.$$
--
--   This is measure-free infrastructure for affine normalization of extended-real convex potentials.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem convex_epigraph_affineSubtract (f : E → EReal) (a : E) (b : ℝ)
--       (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}) :
--       Convex ℝ {p : E × ℝ | affineSubtract f a b p.1 ≤ (p.2 : EReal)}
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Affine`](https://prove2.me/theorems/ba0d4420-d959-4afc-bf5b-05caa7b55a1c).
--
--   Previous: [`legendre_affineSubtract`](https://prove2.me/theorems/86cc89dc-153b-4ec4-a574-1e72902d9a9b) · Next: [`exists_nonnegative_origin_zero_affine`](https://prove2.me/theorems/23dc8e13-df9f-4967-b282-729c3b46dcf2).
--
--   [Source excerpt, lines 91–93](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Affine.lean#L91-L93) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Affine.lean#L90-L121 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Affine`, declaration `FunctionalInequalities.Analysis.convex_epigraph_affineSubtract`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Affine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.convex_epigraph_affineSubtract_readable (f : E → EReal) (a : E) (b : ℝ)
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}) :
    Convex ℝ {p : E × ℝ | affineSubtract f a b p.1 ≤ (p.2 : EReal)} := by sorry
