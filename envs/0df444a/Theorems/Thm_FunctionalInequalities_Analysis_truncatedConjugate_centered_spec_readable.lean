-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_truncatedConjugate_centered_spec_readable
-- name    : FunctionalInequalities.Analysis.truncatedConjugate_centered_spec_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:15.875583+00:00
-- url     : https://prove2.me/theorems/e5ce804e-84d7-49ea-8db6-f2b00ef88634
-- title:
--   Centered Truncated Conjugate Properties
-- statement:
--   This describes the centered truncated conjugate around an interior point.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $u:E\to\mathbb R$ be convex, let $M\in\mathbb R$, and let $x_c\in E$ satisfy $\|x_c\|<M$. Define
--   $$f(p)=u_M^*(p)-\langle p,x_c\rangle+u(x_c).$$
--   Then:
--
--   1. $f(p)\ge0$ for every $p$.
--   2. $f(p)=0$ exactly when $p$ is a subgradient of $u$ at $x_c$:
--      $$f(p)=0\iff\forall y,\ u(x_c)+\langle p,y-x_c\rangle\le u(y).$$
--   3. Every sublevel set $\{p:f(p)\le R\}$ is compact for every $R\in\mathbb R$.
--
--   This provides the compact sublevel structure needed for the contact-set uniqueness argument.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem truncatedConjugate_centered_spec {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {M : ℝ} {xc : E}
--       (hxc : ‖xc‖ < M) :
--       (∀ p, 0 ≤ truncatedConjugate u M p - ⟪p, xc⟫ + u xc) ∧
--       (∀ p, truncatedConjugate u M p - ⟪p, xc⟫ + u xc = 0 ↔ ∀ y, u xc + ⟪p, y - xc⟫ ≤ u y) ∧
--       ∀ R : ℝ, IsCompact {p | truncatedConjugate u M p - ⟪p, xc⟫ + u xc ≤ R}
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Supporting theorems: [`convexOn_truncatedConjugate`](https://prove2.me/theorems/8b13f81e-b6fb-4053-9362-bcc047017760), [`exists_truncatedConjugate_eq`](https://prove2.me/theorems/c5409e58-60c1-4780-bcb8-119d240430ab).
--
--   Previous: [`convexOn_truncatedConjugate`](https://prove2.me/theorems/8b13f81e-b6fb-4053-9362-bcc047017760) · Next: [`isOpen_setOf_truncatedConjugate_maximizer_lt`](https://prove2.me/theorems/88c71aef-4402-44f2-b3b2-345e8d21ce72).
--
--   [Source excerpt, lines 1332–1336](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1332-L1336) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1329-L1426 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.truncatedConjugate_centered_spec`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open Set Metric
open scoped RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.truncatedConjugate_centered_spec_readable {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {M : ℝ} {xc : E}
    (hxc : ‖xc‖ < M) :
    (∀ p, 0 ≤ truncatedConjugate u M p - ⟪p, xc⟫ + u xc) ∧
    (∀ p, truncatedConjugate u M p - ⟪p, xc⟫ + u xc = 0 ↔ ∀ y, u xc + ⟪p, y - xc⟫ ≤ u y) ∧
    ∀ R : ℝ, IsCompact {p | truncatedConjugate u M p - ⟪p, xc⟫ + u xc ≤ R} := by sorry
