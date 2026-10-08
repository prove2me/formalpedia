-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Convex_infDist_isSubanalyticFn
-- name    : NonsmoothLojasiewicz.Convex.infDist_isSubanalyticFn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:50:51.161602+00:00
-- url     : https://prove2.me/theorems/cddf89e7-49fd-4d65-a9cc-120e75b49cb0
-- title:
--   Section 2.1: the distance $d_S$ to a subanalytic set $S$ is subanalytic
-- statement:
--   Let $S\subseteq\mathbb R^n$ be a subanalytic set. Then the distance function
--   $$d_S(x)=\inf\{\|x-a\|:\ a\in S\}$$
--   is a subanalytic function on $\mathbb R^n$.
--
--   The paper recalls this among the elementary properties of subanalytic sets; in the proof of Theorem 3.3 it is applied to $S=\operatorname{crit} f$ before invoking the Łojasiewicz factorization lemma.
--
--   **Formalization Note** $d_S$ is Mathlib's `Metric.infDist`, viewed as an `EReal`-valued function. For $S=\emptyset$ Mathlib returns $0$ (the page's value would be $+\infty$); both functions are subanalytic, so the edge case adds nothing.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1208, Section 2.1, list of properties of subanalytic sets

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic

open Filter Topology

namespace NonsmoothLojasiewicz.Convex

/-- Section 2.1 of Bolte–Daniilidis–Lewis (p. 1208), a recalled property of subanalytic sets:
for a subanalytic set `S ⊆ ℝⁿ`, the distance function `d_S(x) = inf {‖x − a‖ : a ∈ S}` is a
subanalytic function. -/
theorem infDist_isSubanalyticFn {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : NonsmoothLojasiewicz.Continuous.IsSubanalytic S) :
    NonsmoothLojasiewicz.Continuous.IsSubanalyticFn (fun x => ((Metric.infDist x S : ℝ) : EReal)) := by sorry

end NonsmoothLojasiewicz.Convex
