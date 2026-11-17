-- Prove2me | Theorems.Thm_HOTrap_Supplement_theorem_6_1
-- name    : HOTrap.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:31:42.650656+00:00
-- url     : https://prove2.me/theorems/7d81ed4c-2a7b-4f02-b872-6f9032f4b115
-- title:
--   Theorem 6.1 — randomized exact first-order lower bound
-- statement:
--   For every integer $p\ge2$, there is $c_p>0$ such that for all $\Delta,L_1,L_p>0$ there is a finite constant $C_{p,\Delta,L_1,L_p}>0$ with the following property. If
--   $$
--   0<\varepsilon\le c_p\min\left\{(\Delta L_1)^{1/2},\Delta^{p/(p+1)}L_p^{1/(p+1)}\right\}
--   $$
--   and $d\ge C_{p,\Delta,L_1,L_p}\varepsilon^{-(4+2/p)}$, then
--   $$
--   T^{\mathrm{rand}}_{\varepsilon,\mathrm{FO}}\!\left(\mathcal F^{(d)}_{1,p}(\Delta,L_1,L_p)\right)
--   \ge c_p\Delta\sqrt{L_1\gamma_p(\varepsilon)}\,\varepsilon^{-2}.
--   $$
--
--   The oracle returns exact values and gradients, its budget holds for every input and seed, terminal outputs may be arbitrary transcript-measurable points, and success means probability at least $2/3$.
--
--   Differences from the source:
--   - encoding: a real lower bound on integer query complexity → its natural-number ceiling is below the $\mathbb N\cup\{+\infty\}$-valued complexity; reason: this is equivalent and avoids fractional query counts and empty-infimum junk values
--   - encoding: probability of the stationarity event → a measurable inner event of successful seeds with probability at least $2/3$; reason: equivalent for the continuous hard class and makes measurability explicit
--   - encoding: $f(0)-\inf f\le\Delta$ in the hard class → $f(0)-f(y)\le\Delta$ for every $y$; reason: equivalent under the class's nonnegativity condition and avoids a default-valued real infimum
--   - encoding: functions on $\mathbb R^d$ → functions on `EuclideanSpace ℝ (Fin d)`; reason: zero-based finite coordinates carry the same Euclidean norm and derivative structure
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Theorem 6.1, p.37, Eq. (28)

import Mathlib
import Definitions.Def_HOTrap_Supplement_RandomFOAlg
import Definitions.Def_HOTrap_Supplement_effectiveCurvature

namespace HOTrap.Supplement

/-- **Theorem 6.1 (randomized first-order lower bound).** Zhou--Sugiyama--Suzuki,
*Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order
Lower Bounds*, arXiv:2610.02791, Theorem 6.1, p.37 (PDF p.40), Eq. (28).

**Formalization Note.** `c` depends only on `p`; `C` is quantified after `Δ,L₁,L_p` but before
`ε,d`, so it has exactly the printed dependencies.  Since oracle complexity is integer-valued, the
real lower bound is converted with the natural ceiling.  `randFOComplexity` includes exact values
and gradients, Borel transcript rules, an arbitrary transcript-measurable output, an every-seed
budget, and the inner success probability `2/3`. -/
theorem theorem_6_1 (p : ℕ) (hp : 2 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∀ Δ L₁ Lp : ℝ, 0 < Δ → 0 < L₁ → 0 < Lp →
      ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ,
        0 < ε →
        ε ≤ c * min (Real.sqrt (Δ * L₁))
          (Real.rpow Δ ((p : ℝ) / ((p : ℝ) + 1)) *
            Real.rpow Lp (1 / ((p : ℝ) + 1))) →
        ∀ d : ℕ,
          C * Real.rpow ε (-(4 + 2 / (p : ℝ))) ≤ (d : ℝ) →
          ((⌈c * Δ * Real.sqrt (L₁ * effectiveCurvature p L₁ Lp ε) *
              Real.rpow ε (-2)⌉₊ : ℕ) : WithTop ℕ) ≤
            randFOComplexity d (HardClass1p d p Δ L₁ Lp) ε := by sorry

end HOTrap.Supplement
