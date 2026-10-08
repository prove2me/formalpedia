-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Convex_prop213_crit_isSubanalytic
-- name    : NonsmoothLojasiewicz.Convex.prop213_crit_isSubanalytic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:12:30.14798+00:00
-- url     : https://prove2.me/theorems/9eb65e14-c071-4377-a989-bef372fabe1f
-- title:
--   Proposition 2.13(ii): for subanalytic, relatively bounded $f$, $\mathrm{crit}\, f$ is subanalytic
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be subanalytic and **relatively bounded on its domain**, that is, $\{f(x):x\in\operatorname{dom} f\cap B\}$ is bounded for every bounded $B\subseteq\mathbb R^n$. Then the set of critical points
--   $$\operatorname{crit} f=\{x:\ 0\in\partial f(x)\}$$
--   is a subanalytic subset of $\mathbb R^n$.
--
--   Proposition 2.13(ii) also asserts that $\hat\partial f$, $\partial f$ and $m_f$ are subanalytic; this item formalizes the claim on $\operatorname{crit} f$, which the proof of Theorem 3.3 applies to the Moreau envelope $g$.
--
--   **Formalization Note** Relative boundedness (defined in Proposition 2.7, p. 1210) is written: for every bounded $B$ there is $M$ with $|f(x)|\le M$ for all $x\in B$ with $f(x)<+\infty$. $f$ never takes the value $-\infty$.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1211, Proposition 2.13(ii) (claim on crit f); relative boundedness from Proposition 2.7, p. 1210

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit

open Filter Topology
open NonconvexSplitting.Shared

namespace NonsmoothLojasiewicz.Convex

/-- Proposition 2.13(ii) of Bolte–Daniilidis–Lewis (p. 1211), the claim on `crit f`: if
`f : ℝⁿ → ℝ ∪ {+∞}` is subanalytic and relatively bounded on its domain (for every bounded `B`,
`{f(x) : x ∈ dom f ∩ B}` is bounded; Proposition 2.7, p. 1210), then `crit f` is subanalytic. -/
theorem prop213_crit_isSubanalytic {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (hsub : NonsmoothLojasiewicz.Continuous.IsSubanalyticFn f)
    (hrb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ M : ℝ, ∀ x ∈ B, f x ≠ ⊤ → |(f x).toReal| ≤ M) :
    NonsmoothLojasiewicz.Continuous.IsSubanalytic (crit f) := by sorry

end NonsmoothLojasiewicz.Convex
