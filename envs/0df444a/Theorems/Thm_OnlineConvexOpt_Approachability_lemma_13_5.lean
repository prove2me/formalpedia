-- Prove2me | Theorems.Thm_OnlineConvexOpt_Approachability_lemma_13_5
-- name    : OnlineConvexOpt.Approachability.lemma_13_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:42:19.441564+00:00
-- url     : https://prove2.me/theorems/edbb48d3-665d-43b9-ac36-8bfc7e19cc7d
-- title:
--   Lemma 13.5: $\mathrm{Dist}(v,S)=\max_{\|w\|\le 1}\{w^\top v-h_S(w)\}$
-- statement:
--   Let $S\subseteq\mathbb R^d$ be a nonempty, closed, bounded and convex set, with support function $h_S(w)=\max_{x\in S}w^\top x$. For every $v\in\mathbb R^d$,
--
--   $$
--   \mathrm{Dist}(v,S)=\max_{\|w\|\le 1}\bigl\{w^\top v-h_S(w)\bigr\}, \tag{13.1}
--   $$
--
--   and the maximum is attained: some $w$ in the closed unit ball achieves the value $\mathrm{Dist}(v,S)$, and no $w$ in the ball exceeds it.
--
--   This dual description of the distance to a convex set turns the approachability objective into a concave maximization over the unit ball, which is what allows the reduction of Blackwell approachability to online convex optimization (Lemma 13.6, Theorem 13.7).
--
--   **Formalization Note** "max" is encoded by `IsGreatest` of the image of the closed unit ball. $\mathrm{Dist}$ is `Metric.infDist` and $h_S$ is `supportFun`. The book's vector $u$ is called $v$.
--
--   Differences from the source:
--   - encoding: S closed, bounded and convex, with Dist(w,S) = min over S → additionally S.Nonempty; reason: a min over the empty set is undefined; Lean's Metric.infDist w ∅ = 0 would make ∅ approachable
--   - encoding: max_{‖w‖≤1} → IsGreatest of the image of the closed unit ball; reason: the same value with attainment; avoids a real iSup
--   - encoding: h_S(w) = max_{x∈S} w⊤x → supportFun S w := ⨆ s : S, ⟪w, s⟫ (real iSup); reason: for nonempty compact S the iSup is attained and equals the max
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, Lemma 13.5, (13.1), p. 210 (PDF p. 232)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Approachability_supportFun

open scoped InnerProductSpace

namespace OnlineConvexOpt.Approachability

/-- **Lemma 13.5 (distance to a convex set as a maximum over the unit ball), (13.1).**
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, Lemma 13.5,
(13.1), p. 210: "The distance to a set can be written as
Dist(u, S) = max_{‖w‖≤1} { w⊤u − h_S(w) }."

For a nonempty closed bounded convex `S ⊆ ℝ^d` and any `v ∈ ℝ^d`, the distance from `v` to `S`
is the greatest value of `w ↦ ⟪w, v⟫ − h_S(w)` on the closed unit ball: it is attained there and
bounds every value there.

**Formalization Note.**
* "max" is encoded by `IsGreatest` of the image of the closed unit ball, so attainment is part
  of the conclusion (no real `iSup`, which would return junk on an unbounded set).
* `S` is closed, bounded and convex as in the section's standing assumptions (p. 209: "the
  distance to a bounded, closed and convex set S"; p. 210: "support function of closed convex
  set S"). `S` nonempty: the printed `min_{x∈S}` and `max_{x∈S}` are taken over `S`; for
  `S = ∅` both `Metric.infDist` and `supportFun` return the junk value `0`.
* `Dist` is `Metric.infDist`; `h_S` is `supportFun`. The book's vector `u` is called `v`. -/
theorem lemma_13_5 {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hS : IsClosed S)
    (hSb : Bornology.IsBounded S) (hSc : Convex ℝ S) (hSne : S.Nonempty)
    (v : EuclideanSpace ℝ (Fin d)) :
    IsGreatest ((fun w => ⟪w, v⟫_ℝ - supportFun S w) '' Metric.closedBall 0 1)
      (Metric.infDist v S) := by sorry

end OnlineConvexOpt.Approachability
