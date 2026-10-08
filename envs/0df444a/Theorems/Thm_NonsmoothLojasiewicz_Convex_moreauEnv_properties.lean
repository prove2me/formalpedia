-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Convex_moreauEnv_properties
-- name    : NonsmoothLojasiewicz.Convex.moreauEnv_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:12:35.568508+00:00
-- url     : https://prove2.me/theorems/c5b12e20-c5d7-434d-9ada-e15df80595db
-- title:
--   Section 3.2: the envelope $g$ is finite, $C^1$, $g\le f$, $\mathrm{crit}\, g=\mathrm{crit}\, f$, $\inf g=\inf f$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be lower semicontinuous, convex and somewhere finite, and let $g$ be the epigraphical sum of $f$ and $\tfrac12\|\cdot\|^2$,
--   $$g(x)=\inf\Big\{f(u)+\tfrac12\|x-u\|^2:\ u\in\mathbb R^n\Big\}.$$
--   Then $g$ is finite-valued and of class $C^1$, and
--
--   1. (a) $g\le f$;
--   2. (b) the set of critical points of $g$ is exactly the set of critical points of $f$: $\operatorname{crit} g=\operatorname{crit} f$;
--   3. (c) the infimum values coincide: $\inf_{\mathbb R^n} f=\inf_{\mathbb R^n} g$.
--
--   These classical facts of the Moreau regularizing process let the proof of Theorem 3.3 transfer a growth condition from the continuous function $g$ back to $f$.
--
--   **Formalization Note** $\operatorname{crit} g$ uses the limiting subdifferential of $g$ viewed as an `EReal`-valued function; for $C^1$ $g$ this is $\{\nabla g(x)\}$. The infima in (c) are taken in `EReal`. The paper recalls these facts from convex analysis for the functions of Section 3.2; they need no subanalyticity, which is therefore not assumed.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1215, Section 3.2, properties (a)–(c)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit
import Definitions.Def_NonsmoothLojasiewicz_Convex_moreauEnv

open Filter Topology
open NonconvexSplitting.Shared MoreauProx.Characterization

namespace NonsmoothLojasiewicz.Convex

/-- Section 3.2 of Bolte–Daniilidis–Lewis (p. 1215), classical facts on the epigraphical sum `g`
of `f` and `½‖·‖²`, for `f : ℝⁿ → ℝ ∪ {+∞}` lower semicontinuous, convex and somewhere finite:
`g` is finite-valued and `C¹`, and
(a) `g ≤ f`; (b) `crit g = crit f`; (c) `inf f = inf g`. -/
theorem moreauEnv_properties {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) :
    (∃ h : EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ x, moreauEnv f x = (h x : EReal)) ∧ ContDiff ℝ 1 h) ∧
      (∀ x, moreauEnv f x ≤ f x) ∧
      crit (moreauEnv f) = crit f ∧
      (⨅ x, f x) = (⨅ x, moreauEnv f x) := by sorry

end NonsmoothLojasiewicz.Convex
