-- Prove2me | Theorems.Thm_HOTrap_Supplement_theorem_6_5
-- name    : HOTrap.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:32:24.59821+00:00
-- url     : https://prove2.me/theorems/2b9b6c80-1843-4106-a191-54a494477bfd
-- title:
--   Theorem 6.5 — randomized lower bounds without gradient Lipschitzness
-- statement:
--   For every integer $p\ge2$, there are constants $c_p,C_p>0$ such that, whenever
--   $$
--   0<\varepsilon\le c_p\Delta^{p/(p+1)}L_p^{1/(p+1)},
--   $$
--   the following hold.
--
--   1. If $p=2$ and $d\ge C_p(\Delta^{2/3}L_2^{1/3}/\varepsilon)^5$, then
--      $$T^{\mathrm{rand}}_{\varepsilon,\mathrm{FO}}(\mathcal F^{(d)}_2(\Delta,L_2))\ge c_p(\Delta^{2/3}L_2^{1/3}/\varepsilon)^{7/4}.$$
--   2. If $p\ge3$ and $d\ge C_p(\Delta^{p/(p+1)}L_p^{1/(p+1)}/\varepsilon)^{13/3+1/p}$, then
--      $$T^{\mathrm{rand}}_{\varepsilon,\mathrm{FO}}(\mathcal F^{(d)}_p(\Delta,L_p))\ge c_p(\Delta^{p/(p+1)}L_p^{1/(p+1)}/\varepsilon)^{5/3}.$$
--
--   In both branches the hard functions may be chosen $C^\infty$ and coercive.
--
--   Differences from the source:
--   - encoding: real lower bounds on integer query complexity → their natural-number ceilings are below the $\mathbb N\cup\{+\infty\}$-valued complexities; reason: equivalent and avoids fractional query counts
--   - encoding: “the hard functions may be chosen $C^\infty$ and coercive” → each lower bound is also stated for the smooth coercive subclass; reason: complexity of that subclass is the exact minimax content of the sentence
--   - encoding: $f(0)-\inf f\le\Delta$ in the hard class → $f(0)-f(y)\le\Delta$ for every $y$; reason: equivalent under the class's nonnegativity condition and avoids a default-valued real infimum
--   - encoding: probability of the stationarity event → a measurable inner event of successful seeds with probability at least $2/3$; reason: equivalent for the continuous hard class and makes measurability explicit
--   - encoding: functions on $\mathbb R^d$ → functions on `EuclideanSpace ℝ (Fin d)`; reason: zero-based finite coordinates carry the same Euclidean norm and derivative structure
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Theorem 6.5, p.38

import Mathlib
import Definitions.Def_HOTrap_Supplement_RandomFOAlg
import Definitions.Def_HOTrap_Supplement_effectiveCurvature

namespace HOTrap.Supplement

/-- **Theorem 6.5 (lower bounds without gradient Lipschitzness).**
Zhou--Sugiyama--Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping
Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Theorem 6.5, p.38 (PDF p.41).

Both printed branches are stated, including their dimension thresholds.  The parallel bounds for
`SmoothCoercivePart` formalize the theorem's final sentence that the hard functions may be chosen
`C^∞` and coercive.

**Formalization Note.** `c,C` are before every problem parameter and depend only on `p`.  Natural
ceilings express real lower bounds for the integer query complexity without weakening them. -/
theorem theorem_6_5 (p : ℕ) (hp : 2 ≤ p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ Δ Lp ε : ℝ, 0 < Δ → 0 < Lp → 0 < ε →
        ε ≤ c * Real.rpow Δ ((p : ℝ) / ((p : ℝ) + 1)) *
          Real.rpow Lp (1 / ((p : ℝ) + 1)) →
        (p = 2 → ∀ d : ℕ,
          C * Real.rpow
              ((Real.rpow Δ (2 / 3 : ℝ) * Real.rpow Lp (1 / 3 : ℝ)) / ε) 5 ≤ (d : ℝ) →
          ((⌈c * Real.rpow
              ((Real.rpow Δ (2 / 3 : ℝ) * Real.rpow Lp (1 / 3 : ℝ)) / ε)
                (7 / 4 : ℝ)⌉₊ : ℕ) : WithTop ℕ) ≤
              randFOComplexity d (HardClassP d 2 Δ Lp) ε ∧
          ((⌈c * Real.rpow
              ((Real.rpow Δ (2 / 3 : ℝ) * Real.rpow Lp (1 / 3 : ℝ)) / ε)
                (7 / 4 : ℝ)⌉₊ : ℕ) : WithTop ℕ) ≤
              randFOComplexity d (SmoothCoercivePart (HardClassP d 2 Δ Lp)) ε) ∧
        (3 ≤ p → ∀ d : ℕ,
          C * Real.rpow
              ((Real.rpow Δ ((p : ℝ) / ((p : ℝ) + 1)) *
                Real.rpow Lp (1 / ((p : ℝ) + 1))) / ε)
              (13 / 3 + 1 / (p : ℝ)) ≤ (d : ℝ) →
          ((⌈c * Real.rpow
              ((Real.rpow Δ ((p : ℝ) / ((p : ℝ) + 1)) *
                Real.rpow Lp (1 / ((p : ℝ) + 1))) / ε) (5 / 3 : ℝ)⌉₊ : ℕ) :
                WithTop ℕ) ≤ randFOComplexity d (HardClassP d p Δ Lp) ε ∧
          ((⌈c * Real.rpow
              ((Real.rpow Δ ((p : ℝ) / ((p : ℝ) + 1)) *
                Real.rpow Lp (1 / ((p : ℝ) + 1))) / ε) (5 / 3 : ℝ)⌉₊ : ℕ) :
                WithTop ℕ) ≤
            randFOComplexity d (SmoothCoercivePart (HardClassP d p Δ Lp)) ε) := by sorry

end HOTrap.Supplement
