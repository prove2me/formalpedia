-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_truncatedConjugate_eq_readable
-- name    : FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:47.706705+00:00
-- url     : https://prove2.me/theorems/c5409e58-60c1-4780-bcb8-119d240430ab
-- title:
--   Attainment of the Truncated Conjugate
-- statement:
--   This states attainment and domination for a truncated conjugate.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $u:E\to\mathbb R$ be continuous, let $M\ge0$, and let $p\in E$. The supremum over the closed ball $\overline B(0,M)$ is attained: there exists $x\in\overline B(0,M)$ such that
--
--   $$
--   \operatorname{truncatedConjugate}(u,M,p)=\langle p,x\rangle-u(x).
--   $$
--
--   Moreover, every point of the ball gives a value no larger than the truncated conjugate:
--
--   $$
--   \forall y\in\overline B(0,M),\qquad \langle p,y\rangle-u(y)\le\operatorname{truncatedConjugate}(u,M,p).
--   $$
--
--   The declaration is `exists_truncatedConjugate_eq_readable`. It is a compactness result and does not assert attainment of the unrestricted Legendre transform.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_truncatedConjugate_eq {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) (p : E) :
--       (∃ x ∈ closedBall (0 : E) M, truncatedConjugate u M p = ⟪p, x⟫ - u x) ∧
--         ∀ x ∈ closedBall (0 : E) M, ⟪p, x⟫ - u x ≤ truncatedConjugate u M p
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Previous: [`exists_exposed_contact_of_lt`](https://prove2.me/theorems/955fb26b-d452-446f-81e7-00212e58fa6b) · Next: [`convexOn_truncatedConjugate`](https://prove2.me/theorems/8b13f81e-b6fb-4053-9362-bcc047017760).
--
--   [Source excerpt, lines 1292–1294](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1292-L1294) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1291-L1306 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.exists_truncatedConjugate_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open Set Metric
open scoped RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) (p : E) :
    (∃ x ∈ closedBall (0 : E) M, truncatedConjugate u M p = ⟪p, x⟫ - u x) ∧
      ∀ x ∈ closedBall (0 : E) M, ⟪p, x⟫ - u x ≤ truncatedConjugate u M p := by sorry
