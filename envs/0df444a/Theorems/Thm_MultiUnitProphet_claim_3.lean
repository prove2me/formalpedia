-- Prove2me | Theorems.Thm_MultiUnitProphet_claim_3
-- name    : MultiUnitProphet.claim_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:12:22.813607+00:00
-- url     : https://prove2.me/theorems/46c81851-52c8-4036-bc66-352e8b2a93c1
-- title:
--   Claim 3 — the hyperbola $xy+a(x+y)=b$ meets $[0,1]^2$ along a convex (resp. concave) decreasing segment
-- statement:
--   Let $a,b\in\mathbb R$ and $g(x)=\dfrac{b-ax}{x+a}$, the hyperbola $xy+a(x+y)=b$ written as $y=g(x)$.
--
--   1. If $a,b>0$ and $2a+1-b>0$: every point $(x,y)\in[0,1]^2$ of the hyperbola has $y=g(x)$, and $g$ is convex and strictly decreasing on $[0,1]$.
--   2. If $a,b<0$ and $2a+1-b<0$: every point $(x,y)\in[0,1]^2$ of the hyperbola has $x<-a$ and $y=g(x)$, and $g$ is concave and strictly decreasing on $(-\infty,-a)$.
--
--   So the part of the hyperbola inside the unit square is a convex decreasing curve in the first case and a concave decreasing curve in the second. Claim 2 uses this to locate the optima of (Min-Revenue).
--
--   Differences from the source:
--   - generalization: the segment of g intersecting [0, 1]² is convex and decreasing → g is convex and strictly decreasing on all of [0, 1] (case 1) and concave and strictly decreasing on the whole branch x < −a (case 2); reason: the segment inside the square lies over these sets
--   - reading: expressing the hyperbola as y = g(x); the segment intersecting [0, 1]² (in case 2: the concave one) → every point of the hyperbola in [0, 1]² satisfies y = g(x), and in case 2 also x < −a; reason: this is the conclusion of the proof: x ≠ −a, and in case 2 the convex branch misses the square
--   - reading: decreasing → StrictAntiOn; reason: the proof shows dy/dx < 0
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, Claim 3, p.13

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Claim 3: the hyperbola `xy + a(x + y) = b` meets `[0,1]²` along a convex (resp. concave)
decreasing segment.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, Claim 3, p.13: "Let a, b ∈ R, and consider the hyperbola in the x, y plane given by
xy + a(x + y) = b. Expressing it as y = g(x), and considering the segment(s) of g that intersect
the region [0, 1]², the following holds: • when a, b > 0, and 2a + 1 − b > 0, the segment of g
intersecting [0, 1]² is convex and decreasing. • when a, b < 0, and 2a + 1 − b < 0, the segment of g
intersecting [0, 1]² is concave and decreasing."

With `g(x) = (b − ax)/(x + a)`:
1. if `a, b > 0` and `2a + 1 − b > 0`, every point of the hyperbola in `[0,1]²` has `y = g(x)`, and `g`
   is convex and strictly decreasing on `[0, 1]`;
2. if `a, b < 0` and `2a + 1 − b < 0`, every point of the hyperbola in `[0,1]²` has `x < −a` and
   `y = g(x)`, and `g` is concave and strictly decreasing on `(−∞, −a)`.

**Formalization Note.** The segment(s) meeting `[0,1]²` lie in the graph of `g` over `[0, 1]`
(case 1) and over the branch `x < −a` (case 2); the convexity and monotonicity are stated on those
whole sets. -/
theorem claim_3 (a b : ℝ) :
    (0 < a → 0 < b → 0 < 2 * a + 1 - b →
      (∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 → x * y + a * (x + y) = b →
          y = (b - a * x) / (x + a)) ∧
      ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun x => (b - a * x) / (x + a)) ∧
      StrictAntiOn (fun x => (b - a * x) / (x + a)) (Set.Icc (0 : ℝ) 1)) ∧
    (a < 0 → b < 0 → 2 * a + 1 - b < 0 →
      (∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 → x * y + a * (x + y) = b →
          x < -a ∧ y = (b - a * x) / (x + a)) ∧
      ConcaveOn ℝ (Set.Iio (-a)) (fun x => (b - a * x) / (x + a)) ∧
      StrictAntiOn (fun x => (b - a * x) / (x + a)) (Set.Iio (-a))) := by sorry

end MultiUnitProphet
