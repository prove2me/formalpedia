-- Prove2me | Theorems.Thm_JailletLu_claim3
-- name    : JailletLu.claim3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:29:48.920662+00:00
-- url     : https://prove2.me/theorems/a89018c0-1061-4cf7-a219-aff8ffcf6c72
-- title:
--   Claim 3: $h(y,\cdot)$ convex decreasing, $g(y,\cdot)$ concave increasing on $[0,y]$, $g(\cdot,x)$ increasing on $[x,\infty)$
-- statement:
--   Let $h(y,x)=\frac{y}{y-x}(e^{-x}-e^{-y})$ for $x\ne y$, $h(y,y)=ye^{-y}$, and $g(y,x)=h(y,0)-h(y,x)$. Then:
--   1. for every $y\in[0,1]$, the map $x\mapsto h(y,x)$ is convex and strictly decreasing on $[0,y]$;
--   2. for every $y\in[0,1]$, the map $x\mapsto g(y,x)$ is concave and strictly increasing on $[0,y]$;
--   3. for every $x\ge 0$, the map $y\mapsto g(y,x)$ is nondecreasing on $[x,\infty)$, and strictly increasing there when $x>0$.
--
--   These shape properties drive every estimate of §5.4: concavity of $g$ in its second argument gives the bound by $(s_a/\beta_a)g(f_a,\beta_a)$, convexity of $h$ gives inequality (5), and monotonicity in the first argument lets $f_{a_1}$ be replaced by $1$.
--
--   Differences from the source:
--   - reading: "decreasing" / "increasing" in x ∈ [0, y] → strictly decreasing (StrictAntiOn) / strictly increasing (StrictMonoOn); reason: the stronger reading, true for y ∈ [0, 1] (at y = 0 the interval is a point)
--   - reading: "g(y, x) is increasing in y ∈ [x, ∞)" → nondecreasing (MonotoneOn) in y on [x, ∞) for every x ≥ 0, and strictly increasing (StrictMonoOn) for every x > 0; reason: g(y, 0) = 0 for every y, so the strict reading is false at x = 0 and true for x > 0; the two conjuncts imply each reading wherever it holds; the preamble "y ∈ [0, 1]" cannot bind this clause, where y ranges over [x, ∞)
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, Claim 3, p. 15

import Mathlib
import Definitions.Def_JailletLu_h
import Definitions.Def_JailletLu_g

namespace JailletLu

/-- **Claim 3: shape of `h` and `g`.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, Claim 3, p. 15: "For y ∈ [0, 1], h(y, x) is convex and decreasing in x ∈ [0, y];
g(y, x) is concave and increasing in x ∈ [0, y]; g(y, x) is increasing in y ∈ [x, ∞)."

Conclusion:
1. for `y ∈ [0, 1]`, `x ↦ h(y, x)` is convex and strictly decreasing on `[0, y]`, and
   `x ↦ g(y, x)` is concave and strictly increasing on `[0, y]`;
2. for every `x ≥ 0`, `y ↦ g(y, x)` is (weakly) increasing on `[x, ∞)`, and strictly increasing
   there when `x > 0`.

**Formalization Note.** "decreasing"/"increasing" in the first two clauses is read strictly (the
stronger reading, true). In the third clause the strict reading is false at `x = 0` (`g(y, 0) = 0`
for every `y`), so it is stated weakly for every `x ≥ 0` and strictly for every `x > 0`, which
implies each reading wherever it holds. The third clause is stated for every `x ≥ 0`; the preamble
"y ∈ [0, 1]" cannot bind it, since there `y` ranges over `[x, ∞)`. -/
theorem claim3 :
    (∀ y : ℝ, 0 ≤ y → y ≤ 1 →
      ConvexOn ℝ (Set.Icc 0 y) (h y) ∧ StrictAntiOn (h y) (Set.Icc 0 y) ∧
      ConcaveOn ℝ (Set.Icc 0 y) (g y) ∧ StrictMonoOn (g y) (Set.Icc 0 y)) ∧
    (∀ x : ℝ, 0 ≤ x → MonotoneOn (fun y => g y x) (Set.Ici x)) ∧
    (∀ x : ℝ, 0 < x → StrictMonoOn (fun y => g y x) (Set.Ici x)) := by sorry

end JailletLu
