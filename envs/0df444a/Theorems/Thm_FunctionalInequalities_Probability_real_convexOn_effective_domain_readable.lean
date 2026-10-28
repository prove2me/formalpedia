-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_real_convexOn_effective_domain_readable
-- name    : FunctionalInequalities.Probability.real_convexOn_effective_domain_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:45.088581+00:00
-- url     : https://prove2.me/theorems/f7c7760e-e128-40c5-a6ce-efaac3655fcc
-- title:
--   Real Convexity On The Effective Domain
-- statement:
--   This statement extracts ordinary real convexity from an extended-real convex epigraph.
--
--   Let $E$ be a real inner-product normed additive group and let $\phi:E\to\overline{\mathbb R}$. Assume:
--
--   1. $\phi(x)\ge 0$ for every $x\in E$.
--   2. The real epigraph
--      $$\{(x,t)\in E\times\mathbb R:\phi(x)\le t\}$$
--      is convex.
--
--   Then the function $x\mapsto(\phi(x)).\operatorname{toReal}$ is `ConvexOn` on the effective domain
--   $$\{x\in E:\phi(x)\ne+\infty\}.$$
--
--   This is a technical bridge between extended-real convex potentials and ordinary real convex-analysis results.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma real_convexOn_effective_domain {φ : E → EReal} (h0 : ∀ x, 0 ≤ φ x)
--       (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) :
--       ConvexOn ℝ {x | φ x ≠ ⊤} (fun x => (φ x).toReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/ConvexSupport`](https://prove2.me/theorems/883cc35c-d1e7-4fcf-9935-3f624629687e).
--
--   Previous: [`exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure`](https://prove2.me/theorems/2e3067a3-8fdf-4402-9d95-d8eb776cd1f3) · Next: [`strict_sublevel_convex_and_interior`](https://prove2.me/theorems/463b9839-1217-4882-805b-3a7aca81934e).
--
--   [Source excerpt, lines 541–543](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L541-L543) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L539-L559 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `FunctionalInequalities.Probability.real_convexOn_effective_domain`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma FunctionalInequalities.Probability.real_convexOn_effective_domain_readable {φ : E → EReal} (h0 : ∀ x, 0 ≤ φ x)
    (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) :
    ConvexOn ℝ {x | φ x ≠ ⊤} (fun x => (φ x).toReal) := by sorry
