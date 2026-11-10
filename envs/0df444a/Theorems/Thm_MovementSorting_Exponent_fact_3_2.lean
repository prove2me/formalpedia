-- Prove2me | Theorems.Thm_MovementSorting_Exponent_fact_3_2
-- name    : MovementSorting.Exponent.fact_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:02:11.875246+00:00
-- url     : https://prove2.me/theorems/db018a69-451c-4af2-8d7a-236d3808cae6
-- title:
--   Fact 3.2 — a sequence through W is at least half the sum of nearest-neighbour distances
-- statement:
--   Let $Y$ be a metric space and $W \subseteq Y$ finite with $|W| \ge 2$. For $w \in W$ let $\nu_W(w) = \min_{w' \in W\setminus\{w\}} \mathrm{dist}(w,w')$. Then every finite sequence of points of $Y$ that contains every point of $W$ has length (sum of the distances between consecutive points) at least $\tfrac12\sum_{w \in W}\nu_W(w)$.
--
--   Differences from the source:
--   - encoding: Y a metric space, W ⊆ Y finite → [MetricSpace Y] [DecidableEq Y], W : Finset Y, the sequence a List Y; reason: decidable equality only serves to form W ∖ {w}; every type has it classically
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Fact 3.2, p. 10

import Definitions.Def_MovementSorting_Exponent_Geometry

set_option autoImplicit false

namespace MovementSorting.Exponent

/-- Fact 3.2 (p. 10): in a metric space, every finite sequence containing every point of a finite
`W` with `|W| ≥ 2` has length at least `½ Σ_{w ∈ W} ν_W(w)`. -/
theorem fact_3_2 {Y : Type*} [MetricSpace Y] [DecidableEq Y] (W : Finset Y) (hW : 2 ≤ W.card)
    (s : List Y) (hs : ∀ w ∈ W, w ∈ s) :
    (1 / 2 : ℝ) * ∑ w ∈ W, nnDist W w ≤ pathLength s := by sorry

end MovementSorting.Exponent
