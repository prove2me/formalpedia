-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_resolvent_preimage_near_readable
-- name    : FunctionalInequalities.Analysis.resolvent_preimage_near_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:23.337566+00:00
-- url     : https://prove2.me/theorems/253f1fd8-dbe8-46e5-8918-38675b5d625a
-- title:
--   Local Preimage Control for a Firmly Monotone Resolvent
-- statement:
--   This lemma is a technical local inverse estimate.
--
--   Let $E$ be a real inner-product space, let $P:E\to E$, and assume the firm monotonicity inequality
--
--   $$\|P(a)-P(b)\|^2\le\langle P(a)-P(b),a-b\rangle.$$
--
--   Let $z\in E$ and let $c,\delta>0$. Suppose that every $w$ with $\|w-z\|<\delta$ satisfies
--
--   $$c\|w-z\|\le\|P(w)-P(z)\|.$$
--
--   Then any $a\in E$ satisfying
--
--   $$\|P(a)-P(z)\|<\frac{c^2\delta}{2}$$
--
--   must also satisfy
--
--   $$\|a-z\|<\delta.$$
--
--   The auxiliary declaration `resolvent_preimage_near_readable` is used to transfer a sufficiently small image neighborhood into the corresponding domain neighborhood.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 800000 in
--   private lemma resolvent_preimage_near {P : E → E} {z : E}
--       (hm : ∀ a b, ‖P a - P b‖ ^ 2 ≤ ⟪P a - P b, a - b⟫)
--       {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
--       (hl : ∀ w, ‖w - z‖ < δ → c * ‖w - z‖ ≤ ‖P w - P z‖)
--       (a : E) (ha : ‖P a - P z‖ < c ^ 2 * δ / 2) :
--       ‖a - z‖ < δ
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/SecondOrder`](https://prove2.me/theorems/25ef7ab1-0f22-4192-9c58-d196bc21f161).
--
--   Next: [`subgradient_expansion_of_hasFDerivAt_resolvent`](https://prove2.me/theorems/87eddc48-68f3-46a2-9e7f-49882aba3799).
--
--   [Source excerpt, lines 73–79](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L73-L79) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L73-L124 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondOrder`, declaration `_private.FunctionalInequalities.Analysis.Convex.SecondOrder.0.FunctionalInequalities.Analysis.resolvent_preimage_near`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondOrder

open scoped RealInnerProductSpace Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 800000

lemma FunctionalInequalities.Analysis.resolvent_preimage_near_readable {P : E → E} {z : E}
    (hm : ∀ a b, ‖P a - P b‖ ^ 2 ≤ ⟪P a - P b, a - b⟫)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hl : ∀ w, ‖w - z‖ < δ → c * ‖w - z‖ ≤ ‖P w - P z‖)
    (a : E) (ha : ‖P a - P z‖ < c ^ 2 * δ / 2) :
    ‖a - z‖ < δ := by sorry
