-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_isOpen_setOf_truncatedConjugate_maximizer_lt_readable
-- name    : FunctionalInequalities.Analysis.isOpen_setOf_truncatedConjugate_maximizer_lt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:09.454654+00:00
-- url     : https://prove2.me/theorems/88c71aef-4402-44f2-b3b2-345e8d21ce72
-- title:
--   Open Slopes With Interior Truncated Maximizers
-- statement:
--   This proves openness of a set of admissible slopes for the truncated conjugate.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $u:E\to\mathbb R$ be continuous, and let $M\in\mathbb R$ satisfy $0\le M$. Define the set of slopes $p$ such that every maximizer $x$ in the closed ball $\overline B(0,M)$ of `truncatedConjugate` satisfies $\|x\|<M$:
--   $$\left\{p:\forall x\in\overline B(0,M),\quad u_M^*(p)=\langle p,x\rangle-u(x)\Rightarrow\|x\|<M\right\}.$$
--   This set is open.
--
--   The result is a technical topological ingredient for identifying subgradient images of the truncated conjugate.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem isOpen_setOf_truncatedConjugate_maximizer_lt {u : E → ℝ} (hu : Continuous u) {M : ℝ}
--       (hM : 0 ≤ M) :
--       IsOpen {p : E | ∀ x ∈ closedBall (0 : E) M,
--         truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M}
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Supporting theorems: [`convexOn_truncatedConjugate`](https://prove2.me/theorems/8b13f81e-b6fb-4053-9362-bcc047017760).
--
--   Previous: [`truncatedConjugate_centered_spec`](https://prove2.me/theorems/e5ce804e-84d7-49ea-8db6-f2b00ef88634) · Next: [`n7_subgradient_eq_maximizer`](https://prove2.me/theorems/7f300c00-6c7e-43ce-894b-43082cb54e74).
--
--   [Source excerpt, lines 1552–1555](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1552-L1555) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1551-L1574 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.isOpen_setOf_truncatedConjugate_maximizer_lt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open Set Metric
open scoped RealInnerProductSpace Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.isOpen_setOf_truncatedConjugate_maximizer_lt_readable {u : E → ℝ} (hu : Continuous u) {M : ℝ}
    (hM : 0 ≤ M) :
    IsOpen {p : E | ∀ x ∈ closedBall (0 : E) M,
      truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M} := by sorry
