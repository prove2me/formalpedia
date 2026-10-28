-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_n7_subgradient_eq_maximizer_readable
-- name    : FunctionalInequalities.Analysis.n7_subgradient_eq_maximizer_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:02.070361+00:00
-- url     : https://prove2.me/theorems/7f300c00-6c7e-43ce-894b-43082cb54e74
-- title:
--   Truncated Conjugate Subgradient Identifies Maximizer
-- statement:
--   This is an auxiliary uniqueness statement for truncated conjugate maximizers.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $u:E\to\mathbb R$ be continuous and strictly convex, and let $M\ge0$. Let $p,x,g\in E$ satisfy:
--
--   1. $\|x\|<M$.
--   2. $p$ is a subgradient of $u$ at $x$.
--   3. The truncated conjugate satisfies
--      $$u_M^*(p)=\langle p,x\rangle-u(x).$$
--   4. $g$ is a subgradient of the truncated conjugate at $p$:
--      $$u_M^*(p)+\langle g,q-p\rangle\le u_M^*(q)\quad\text{for all }q.$$
--
--   Then
--   $$g=x.$$
--
--   The lemma is used in the identification of the subgradient image of the truncated conjugate.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma n7_subgradient_eq_maximizer {u : E → ℝ}
--       (hu : Continuous u) (hstrict : StrictConvexOn ℝ univ u)
--       {M : ℝ} (hM : 0 ≤ M) {p x g : E} (hx : ‖x‖ < M)
--       (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y)
--       (heq : truncatedConjugate u M p = ⟪p, x⟫ - u x)
--       (hg : ∀ q, truncatedConjugate u M p + ⟪g, q - p⟫ ≤ truncatedConjugate u M q) :
--       g = x
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Supporting theorems: [`convexOn_truncatedConjugate`](https://prove2.me/theorems/8b13f81e-b6fb-4053-9362-bcc047017760), [`exists_truncatedConjugate_eq`](https://prove2.me/theorems/c5409e58-60c1-4780-bcb8-119d240430ab).
--
--   Previous: [`isOpen_setOf_truncatedConjugate_maximizer_lt`](https://prove2.me/theorems/88c71aef-4402-44f2-b3b2-345e8d21ce72) · Next: [`subgradientImage_truncatedConjugate_eq`](https://prove2.me/theorems/e685fa4c-013a-44d7-b25b-31318e3dcf54).
--
--   [Source excerpt, lines 1598–1604](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1598-L1604) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1598-L1655 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `_private.FunctionalInequalities.Analysis.Convex.Caffarelli.0.FunctionalInequalities.Analysis.n7_subgradient_eq_maximizer`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open Set Metric
open scoped RealInnerProductSpace Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

lemma FunctionalInequalities.Analysis.n7_subgradient_eq_maximizer_readable {u : E → ℝ}
    (hu : Continuous u) (hstrict : StrictConvexOn ℝ univ u)
    {M : ℝ} (hM : 0 ≤ M) {p x g : E} (hx : ‖x‖ < M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y)
    (heq : truncatedConjugate u M p = ⟪p, x⟫ - u x)
    (hg : ∀ q, truncatedConjugate u M p + ⟪g, q - p⟫ ≤ truncatedConjugate u M q) :
    g = x := by sorry
