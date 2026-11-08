-- Prove2me | Theorems.Thm_GraphNNSphere_eq_9_chernoff
-- name    : GraphNNSphere.eq_9_chernoff
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:25.43058+00:00
-- url     : https://prove2.me/theorems/3fba5af1-0764-4eb0-bf34-7b2d74499f4a
-- title:
--   Eq. (9) — Chernoff bounds for the binomial law
-- statement:
--   For $B\sim\mathrm{Bin}(N,p)$ with mean $\mu=Np>0$ and $s>0$,
--   $$P(B\ge\mu+s)\le\exp\Bigl(-\frac{s^2}{2(\mu+s/3)}\Bigr)\quad\text{and}\quad P(B\le\mu-s)\le\exp\Bigl(-\frac{s^2}{2\mu}\Bigr).$$
--
--   These control deviations of the ranks in (8) from their means.
--
--   Differences from the source:
--   - encoding: P(B ≥ μ + s) and P(B ≤ μ − s) → finite sums of the binomial mass over m ∈ {0, …, N}; reason: the same numbers
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.4, Eq. (9), p.18

import Mathlib
import Definitions.Def_GraphNNSphere_binomMass

namespace GraphNNSphere

/-- Eq. (9), Chernoff bounds for `B ~ Bin(N, p)` with mean `μ = Np > 0` and `s > 0` (Lu, *Sharp
Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript
sha256 93565bc5…), §2.4, Eq. (9), p.18).

**Formalization Note** The two tail probabilities are written as finite sums of the binomial mass
over `m ∈ {0, …, N}`. -/
theorem eq_9_chernoff (N : ℕ) (p s : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hμ : 0 < (N : ℝ) * p)
    (hs : 0 < s) :
    ∑ m ∈ (Finset.range (N + 1)).filter (fun m : ℕ => (N : ℝ) * p + s ≤ (m : ℝ)), binomMass N p m ≤
        Real.exp (-(s ^ 2 / (2 * ((N : ℝ) * p + s / 3)))) ∧
    ∑ m ∈ (Finset.range (N + 1)).filter (fun m : ℕ => (m : ℝ) ≤ (N : ℝ) * p - s), binomMass N p m ≤
        Real.exp (-(s ^ 2 / (2 * ((N : ℝ) * p)))) := by sorry

end GraphNNSphere
