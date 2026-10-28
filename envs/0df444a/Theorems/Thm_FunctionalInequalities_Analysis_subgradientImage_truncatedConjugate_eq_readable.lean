-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_truncatedConjugate_eq_readable
-- name    : FunctionalInequalities.Analysis.subgradientImage_truncatedConjugate_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:59.319067+00:00
-- url     : https://prove2.me/theorems/e685fa4c-013a-44d7-b25b-31318e3dcf54
-- title:
--   Truncated Conjugate Image Identification
-- statement:
--   This gives the Danskin-type identification of a truncated-conjugate subgradient image.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $u:E\to\mathbb R$ be continuous and strictly convex, and let $M\ge0$. Let $S\subseteq E$ satisfy the interior-maximizer condition: for every $p\in S$ and every $x\in\overline B(0,M)$,
--   $$u_M^*(p)=\langle p,x\rangle-u(x)\Longrightarrow\|x\|<M.$$
--   Then
--   $$\partial(u_M^*)(S)=\left\{x:\exists p\in S,\ \forall y,\ u(x)+\langle p,y-x\rangle\le u(y)\right\}.$$
--
--   This result converts a subgradient image of the truncated conjugate into an inverse subgradient image of $u$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem subgradientImage_truncatedConjugate_eq {u : E → ℝ} (hu : Continuous u)
--       (hstrict : StrictConvexOn ℝ univ u) {M : ℝ} (hM : 0 ≤ M) {S : Set E}
--       (hS : ∀ p ∈ S, ∀ x ∈ closedBall (0 : E) M, truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M) :
--       subgradientImage (truncatedConjugate u M) S = {x | ∃ p ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y}
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`exists_truncatedConjugate_eq`](https://prove2.me/theorems/c5409e58-60c1-4780-bcb8-119d240430ab), [`n7_subgradient_eq_maximizer`](https://prove2.me/theorems/7f300c00-6c7e-43ce-894b-43082cb54e74).
--
--   Previous: [`n7_subgradient_eq_maximizer`](https://prove2.me/theorems/7f300c00-6c7e-43ce-894b-43082cb54e74) · Next: [`eq_of_two_contacts_below`](https://prove2.me/theorems/1bde12d1-3df1-4935-9ced-e218f57c79c3).
--
--   [Source excerpt, lines 1661–1664](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1661-L1664) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1657-L1687 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.subgradientImage_truncatedConjugate_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open Set Metric
open scoped RealInnerProductSpace Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.subgradientImage_truncatedConjugate_eq_readable {u : E → ℝ} (hu : Continuous u)
    (hstrict : StrictConvexOn ℝ univ u) {M : ℝ} (hM : 0 ≤ M) {S : Set E}
    (hS : ∀ p ∈ S, ∀ x ∈ closedBall (0 : E) M, truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M) :
    subgradientImage (truncatedConjugate u M) S = {x | ∃ p ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by sorry
