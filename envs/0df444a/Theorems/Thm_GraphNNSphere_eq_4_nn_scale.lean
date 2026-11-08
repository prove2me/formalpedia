-- Prove2me | Theorems.Thm_GraphNNSphere_eq_4_nn_scale
-- name    : GraphNNSphere.eq_4_nn_scale
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:43:19.359568+00:00
-- url     : https://prove2.me/theorems/32d9ea13-b049-4c32-a2d3-c4995d810952
-- title:
--   Eq. (4) — the nearest-neighbor scale $\theta_1$ in both regimes
-- statement:
--   Let $\theta_1$ be defined by $nF_{d-1}(\theta_1)=1$.
--
--   In the logarithmic regime $d=\lfloor c\log n\rfloor$, $\theta_1$ stays bounded away from $\pi/2$ and
--   $$\sin\theta_1=e^{-1/c}\bigl(1+O(\log d/d)\bigr).$$
--
--   In the dense regime, $\theta_1\to0$ (so it is also bounded away from $\pi/2$), and
--   $$\frac1{\sin\theta_1}=n^{1/(d-1)}\bigl(1+O(\log d/d)\bigr),\qquad\log\frac1{\theta_1}=(1+o(1))\frac{\log n}{d-1}=o(d).$$
--
--   This gives the scale of the exact nearest-neighbor distance, bounded in the first regime and vanishing in the second.
--
--   Differences from the source:
--   - encoding: O(log d/d), (1 + o(1)) and o(d) → an explicit bound C log d/d for large n, and the limits of the ratios; reason: the standard meaning of the asymptotic notation at this quantifier position (§2.1)
--   - reading: constants unspecified → C depends only on c in the logarithmic clause and is absolute in the dense clause, before the sequence d; only the threshold depends on d; reason: the convention of §2.1, the stronger reading, which the estimate gives
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.2, Eq. (4), p.15

import Mathlib
import Definitions.Def_GraphNNSphere_theta1
import Definitions.Def_GraphNNSphere_logDim
import Definitions.Def_GraphNNSphere_IsDenseRegime

open Filter Topology

namespace GraphNNSphere

/-- The nearest-neighbor scale, including Eq. (4) (Lu, *Sharp Limits of Graph-Based Nearest Neighbor
Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §2.2, Eq. (4), p.15).

**Formalization Note** `O(log d / d)` is an explicit bound `C log d / d` for large `n`. The first
clause is the logarithmic regime, with `C` and the bound `θmax < π/2` depending on `c`. The second is
the dense regime, with `C` absolute and only the threshold depending on the sequence `d`; there
`θ₁ → 0` gives "bounded away from `π/2`". -/
theorem eq_4_nn_scale :
    (∀ c : ℝ, 0 < c → ∃ θmax : ℝ, θmax < Real.pi / 2 ∧ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      theta1 n (logDim c n) ≤ θmax ∧
      |Real.sin (theta1 n (logDim c n)) / Real.exp (-1 / c) - 1| ≤
        C * Real.log (logDim c n : ℝ) / (logDim c n : ℝ)) ∧
    (∃ C : ℝ, ∀ d : ℕ → ℕ, IsDenseRegime d →
      Tendsto (fun n : ℕ => theta1 n (d n)) atTop (𝓝 0) ∧
      (∀ᶠ n : ℕ in atTop,
        |(1 / Real.sin (theta1 n (d n))) / (n : ℝ) ^ (1 / ((d n : ℝ) - 1)) - 1| ≤
          C * Real.log (d n : ℝ) / (d n : ℝ)) ∧
      Tendsto (fun n : ℕ => Real.log (1 / theta1 n (d n)) /
          (Real.log (n : ℝ) / ((d n : ℝ) - 1))) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => Real.log (1 / theta1 n (d n)) / (d n : ℝ)) atTop (𝓝 0)) := by sorry

end GraphNNSphere
