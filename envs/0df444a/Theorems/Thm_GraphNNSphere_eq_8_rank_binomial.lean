-- Prove2me | Theorems.Thm_GraphNNSphere_eq_8_rank_binomial
-- name    : GraphNNSphere.eq_8_rank_binomial
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:47.794181+00:00
-- url     : https://prove2.me/theorems/c0a52adb-0359-44f8-9d9b-6b085f06d28b
-- title:
--   Eq. (8) — rank is binomial, and $F(\delta(q,x))$ is uniform
-- statement:
--   Let the data be uniform. Fix a label $i$ and a query $q$, and write $x=X_i$. Conditional on $x$ and $q$, the number of other data points closer to $q$ is binomial:
--   $$\mathrm{rank}_q(x)-1\sim\mathrm{Bin}\bigl(n-1,F(\delta(q,x))\bigr).\tag{8}$$
--   Moreover, $F(\delta(q,x))$ is uniform on $[0,1]$ for fixed $q$ and uniform $x$, and for fixed $x$ and uniform $q$.
--
--   These facts relate cap probabilities to ranks and are used when averaging over a point or a query.
--
--   Differences from the source:
--   - encoding: "conditional on x" → the coordinate i is overwritten by x (Function.update), and the event depends only on the other n − 1 coordinates; reason: the coordinates are independent and j = i is never counted, so this is the conditional law
--   - encoding: the law Bin(n − 1, F) → its mass at each m; reason: same law
--   - reading: no range of d printed → d ≥ 2; reason: the paper has d → ∞; for d = 1 the sphere has atoms and the claims fail
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.4, Eq. (8), p.18

import Mathlib
import Definitions.Def_GraphNNSphere_capMass
import Definitions.Def_GraphNNSphere_dataLaw
import Definitions.Def_GraphNNSphere_rank
import Definitions.Def_GraphNNSphere_binomMass

open MeasureTheory

namespace GraphNNSphere

/-- Eq. (8) and the uniform transform (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on
the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §2.4, Eq. (8), p.18).

**Formalization Note** "Conditional on `x`" is `Function.update X i x`: the event depends only on the
other `n - 1` coordinates, as `j = i` is never counted in `rank`. The law `Bin(n - 1, F)` is written
through its mass at each `m`. `d ≥ 2` is needed: for `d = 1` the sphere has atoms, the open and
closed cap masses differ, and neither claim holds. The sets are measurable, and `x ↦ F(δ(q, x))` is
measurable as `F` is monotone, so `Measure.map` is not degenerate. -/
theorem eq_8_rank_binomial (d : ℕ) (hd : 2 ≤ d) :
    (∀ (n : ℕ) (i : Fin n) (q x : Sph d) (m : ℕ),
      (dataLaw n d {X | rank (Function.update X i x) q i = m + 1}).toReal =
        binomMass (n - 1) (capMass d (geo q x)) m) ∧
    (∀ q : Sph d, (unif d).map (fun x => capMass d (geo q x)) =
      (volume : Measure ℝ).restrict (Set.Icc 0 1)) ∧
    (∀ x : Sph d, (unif d).map (fun q => capMass d (geo q x)) =
      (volume : Measure ℝ).restrict (Set.Icc 0 1)) := by sorry

end GraphNNSphere
