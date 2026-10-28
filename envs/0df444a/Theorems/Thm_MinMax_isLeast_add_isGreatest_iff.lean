-- Prove2me | Theorems.Thm_MinMax_isLeast_add_isGreatest_iff
-- name    : MinMax.isLeast_add_isGreatest_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:48:24.139795+00:00
-- url     : https://prove2.me/theorems/16629874-39f7-44a9-bb68-cefa66e281e6
-- title:
--   Minimizing $g(x) + \max W(x)$ and minimizing over $\{g(x)+d : d \in D(x)\}$ have the same value
-- statement:
--   Let $S$ be a set, $g : S \to \mathbb{R}$, and let $W(x), D(x) \subseteq \mathbb{R}$ be two families of reals indexed by $x$. Suppose that for every $x \in S$ there is a single value $w$ that is simultaneously the greatest element of $W(x)$ and the least element of $D(x)$. Then for every $q \in \mathbb{R}$,
--
--   $$
--   q = \min_{x \in S}\ \big(g(x) + \max W(x)\big) \quad\Longleftrightarrow\quad q = \min_{x \in S}\ \min_{d \in D(x)} \big(g(x) + d\big),
--   $$
--
--   where both sides are read as `IsLeast` of the corresponding set of achievable values.
--
--   This is the bookkeeping step at the heart of every two-stage reformulation. The outer problem
--   chooses $x$; the inner problem is a worst case over $W(x)$ -- an adversary, a supremum over a
--   distribution set, a recourse cost -- and strong duality for the inner problem replaces it by a
--   minimization over $D(x)$, the feasible set of its dual. The hypothesis is exactly inner strong
--   duality *with attainment on both sides*, at every $x$. The conclusion is that the two outer
--   problems have the same optimal value, and that one is attained exactly when the other is.
--
--   Stated this way the step is independent of what the inner problem is, which is why it belongs
--   in the library rather than inside each reformulation.
--
--   **Formalization Note** `IsLeast`/`IsGreatest` bundle membership with the bound, so the
--   statement carries attainment rather than just the value; the hypothesis gives, at each $x$, a
--   witness $w$ with `IsGreatest (W x) w ∧ IsLeast (D x) w`, and uniqueness of a greatest element
--   (`IsGreatest.unique`) is what lets the two sets be exchanged.
-- source:
--   Carried as an internal support lemma, with this exact statement and proof, in twelve accepted submissions across ten missions of the OR Formalization Drive (e.g. https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1); published here once so that it can be imported. The inner-problem exchange step of a two-stage or robust optimization reformulation.

import Mathlib

open Matrix

namespace MinMax

theorem isLeast_add_isGreatest_iff {X : Type*} (S : Set X) (g : X → ℝ)
    (W D : X → Set ℝ) (h : ∀ x ∈ S, ∃ w, IsGreatest (W x) w ∧ IsLeast (D x) w) (q : ℝ) :
    IsLeast {v | ∃ x ∈ S, ∃ w, IsGreatest (W x) w ∧ v = g x + w} q ↔
      IsLeast {v | ∃ x ∈ S, ∃ d ∈ D x, v = g x + d} q := by sorry

end MinMax
