-- Prove2me | Theorems.Thm_OfflineToOnline_eq_4_linf_dist_cone
-- name    : OfflineToOnline.eq_4_linf_dist_cone
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:09.725985+00:00
-- url     : https://prove2.me/theorems/412c1dc0-8160-40d9-bcaa-fd83de115528
-- title:
--   Display (4) — $d_\infty(x,S)=\max_{w\in S^\circ,\ \|w\|_1\le1}\langle w,x\rangle$ for a convex cone $S$
-- statement:
--   Let $S\subseteq\mathbb R^d$ be a nonempty convex cone, i.e. a nonempty convex set with $a s\in S$ for all $s\in S$ and $a\ge0$, and let $S^\circ$ be its polar cone. Then for every $x\in\mathbb R^d$ the maximum below is attained and
--
--   $$
--   d_\infty(x,S)=\max_{w\in S^\circ,\ \|w\|_1\le1}\ \langle w,x\rangle ,\qquad d_\infty(x,S)=\inf_{s\in S}\|x-s\|_\infty .
--   $$
--
--   This dual formula turns the $\ell_\infty$ distance of an average payoff from a cone into a linear maximization over $S^\circ\cap B_1(1)$, the decision set of the online linear optimization problem in the $\ell_\infty$ proof of Theorem 1. The Euclidean version $d_2(x,S)=\max_{w\in S^\circ\cap B_2(1)}\langle w,x\rangle$, which the text below (4) derives, is the published theorem `ApproachRegret.ToOLO.lemma13_dist_cone`.
--
--   Differences from the source:
--   - reading: max over w ∈ S°, ‖w‖ ≤ 1 with an unsubscripted norm → max over w ∈ S°, ‖w‖₁ ≤ 1; reason: with ‖·‖₂ the printed d∞ identity is false (S = {0} ⊆ ℝ², x = (1,1): d∞ = 1, max = √2); ℓ1 is the dual norm of ℓ∞, under which it is true; the ℓ2 identity of the text is the published ApproachRegret.ToOLO.lemma13_dist_cone
--   - encoding: convex cone S → nonempty convex set closed under nonnegative scaling; reason: Metric.infDist x ∅ = 0; every cone in the usual sense contains 0
--   - encoding: d∞(x,S) = max … → IsGreatest of the image, i.e. the maximum is attained and equals Metric.infDist x S; reason: states that the max exists
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, display (4), p.46, with footnote 22

import Mathlib
import Definitions.Def_OfflineToOnline_polarCone

namespace OfflineToOnline

/-- **Display (4)**, ℓ∞ reading: for any `x ∈ ℝ^d` and nonempty convex cone `S ⊆ ℝ^d`,
`d∞(x, S) = max_{w ∈ S°, ‖w‖₁ ≤ 1} ⟨w, x⟩`, the maximum being attained.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, (4), p.46, with footnote 22 (polar cone).

Formalization Note: the page writes the constraint as `‖w‖ ≤ 1` without a subscript. With
`‖·‖ = ‖·‖₂` the identity is false for `d∞` (`S = {0} ⊆ ℝ²`, `x = (1, 1)`: `d∞ = 1`, the maximum is
`√2`); with the dual norm `‖·‖₁` of `ℓ∞` it is true, and that is the reading stated here. The
`ℓ2` identity `d₂(x, S) = max_{w ∈ S° ∩ B₂(1)} ⟨w, x⟩` proved in the text below (4) is the
published `ApproachRegret.ToOLO.lemma13_dist_cone`. `Metric.infDist` in `Fin d → ℝ` is `d∞`;
`IsGreatest` says the maximum exists and equals `d∞(x, S)`. A cone is closed under nonnegative
scaling; nonemptiness is required because `Metric.infDist x ∅ = 0`. -/
theorem eq_4_linf_dist_cone {d : ℕ} (S : Set (Fin d → ℝ)) (hSv : Convex ℝ S)
    (hScone : ∀ s ∈ S, ∀ a : ℝ, 0 ≤ a → a • s ∈ S) (hSn : S.Nonempty) (x : Fin d → ℝ) :
    IsGreatest ((fun w : Fin d → ℝ => ∑ j, w j * x j) '' (polarCone S ∩ {w | ∑ j, |w j| ≤ 1}))
      (Metric.infDist x S) := by sorry

end OfflineToOnline
