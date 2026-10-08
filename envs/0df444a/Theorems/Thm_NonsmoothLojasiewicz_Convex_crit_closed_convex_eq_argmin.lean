-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Convex_crit_closed_convex_eq_argmin
-- name    : NonsmoothLojasiewicz.Convex.crit_closed_convex_eq_argmin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:12:06.154013+00:00
-- url     : https://prove2.me/theorems/b8ce02bd-143e-4936-a64a-71df7698f749
-- title:
--   Section 3.2: for lsc convex $f$, $\mathrm{crit}\, f$ is closed, convex and the set of minimizers
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be lower semicontinuous, convex and somewhere finite. Then the set of critical points $\operatorname{crit} f=\{x:0\in\partial f(x)\}$ is closed and convex, and
--   $$\operatorname{crit} f=\{x\in\mathbb R^n:\ f(x)\le f(y)\text{ for all }y\in\mathbb R^n\},$$
--   the set of minimizers of $f$.
--
--   In Theorem 3.3 this is what makes $\min f$ the common value of $f$ on $\operatorname{crit} f$, and $d_S$ with $S=\operatorname{crit} f$ the distance to the solution set.
--
--   **Formalization Note** The paper states this in the standing assumptions of Section 3.2 as a consequence of (5), which needs no subanalyticity; the statement is therefore made for every lower semicontinuous convex somewhere-finite $f$ (`GammaZero f`).
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1215, Section 3.2, first paragraph

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

namespace NonsmoothLojasiewicz.Convex

/-- Section 3.2 of Bolte–Daniilidis–Lewis (p. 1215): for a lower semicontinuous convex function
`f : ℝⁿ → ℝ ∪ {+∞}` that is somewhere finite, the set of critical points `crit f` is closed and
convex and coincides with the set of minimizers of `f`. -/
theorem crit_closed_convex_eq_argmin {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) :
    IsClosed (crit f) ∧ Convex ℝ (crit f) ∧
      crit f = {x | ∀ y, f x ≤ f y} := by sorry

end NonsmoothLojasiewicz.Convex
