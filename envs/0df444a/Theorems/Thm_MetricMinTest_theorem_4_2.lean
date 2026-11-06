-- Prove2me | Theorems.Thm_MetricMinTest_theorem_4_2
-- name    : MetricMinTest.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:46.737648+00:00
-- url     : https://prove2.me/theorems/5bc00dbb-9a19-4f64-9456-be893642d19b
-- title:
--   Theorem 4.2, p.8 — a tight information–certificate gap on $d_m$: $F=k/\gamma^2$, $H=k/(\gamma^2(1+3m/4))$
-- statement:
--   For every integer $m\ge1$ and $\gamma>0$, the critical metric $d_m(x,y)=\gamma(1-2^{-\mathrm{lev}(x,y)})$ on $k=4^m$ points is an ultrametric and satisfies
--   $$F_{d_m}(\gamma)=\frac k{\gamma^2},\qquad H_{d_m}(\gamma)=\frac k{\gamma^2(1+3m/4)}.$$
--   Its distance profile is
--   $$s_{d_m}=\frac{F_{d_m}}{H_{d_m}}=1+\tfrac38\log_2k=\Theta\big(1+\log(\gamma^2H_{d_m}(\gamma))\big),$$
--   its fractional and integral ball-cover optima coincide, and its distance matrix is rational whenever $\gamma$ is rational.
--
--   The theorem gives an exact logarithmic gap between information allocations and single-center threshold covers, on a laminar ball family with no integrality gap.
--
--   **Formalization Note** All clauses are one statement. The $\Theta$ is with absolute constants $c,C>0$ chosen before $m$ and $\gamma$, with the natural logarithm.
--
--   Differences from the source:
--   - encoding: $\Theta(1+\log(\gamma^2H))$ → there are $c,C>0$, chosen before $m$ and $\gamma$, with $c(1+\ln(\gamma^2H))\le s_{d_m}\le C(1+\ln(\gamma^2H))$; reason: quantifier form of $\Theta$ with absolute constants (the paper's convention, p.6)
--   - encoding: "rational" → in the image of $\mathbb Q\to\mathbb R$; reason: Lean convention
--   - encoding: the minima $H_d(\gamma)$ of (1.1) and $F_d(\gamma)$ of (2.1) over indexed balls $B_{j\ell}$ → real infima of the feasible values, with indexed balls encoded by the pairs $(j,i)$ with $d(j,i)<\gamma$; reason: the minima are attained (pp.6–7) and a repeated distance only duplicates a ball at equal cost, so the values are the same
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem 4.2, p.8

import Mathlib
import Definitions.Def_MetricMinTest_dm
import Definitions.Def_MetricMinTest_IsUltrametric
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_certWorkload
import Definitions.Def_MetricMinTest_certWorkloadInt
import Definitions.Def_MetricMinTest_distProfile

namespace MetricMinTest

/-- **Theorem 4.2 (A tight information–certificate gap).** Chen–Fang, *Minimum-Mean Testing under
Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem 4.2, p.8:
"For every integer m ≥ 1 and γ > 0, the ultrametric d_m on k = 4^m points satisfies
F_{d_m}(γ) = k/γ², H_{d_m}(γ) = k/(γ²(1 + 3m/4)). Its distance profile (Theorem 6.1) is
s_{d_m} = F_{d_m}/H_{d_m} = 1 + (3/8) log₂ k = Θ(1 + log(γ² H_{d_m}(γ))). Its fractional and
integral ball-cover optima coincide, and its distance matrix is rational whenever γ is rational."

**Formalization Note.** All clauses are in one statement. The `Θ` is with absolute constants
`c, C > 0` chosen before `m` and `γ`, natural logarithm. "`d_m` is an ultrametric on `k = 4^m`
points" is the clause `IsUltrametric (dm m γ)` together with the index type `Fin m → Fin 4`.
"Rational" is membership in the range of `ℚ → ℝ`. -/
theorem theorem_4_2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ γ : ℝ, 0 < γ →
      IsUltrametric (dm m γ) ∧
      certWorkload (dm m γ) γ = (4 : ℝ) ^ m / γ ^ 2 ∧
      infoWorkload (dm m γ) γ = (4 : ℝ) ^ m / (γ ^ 2 * (1 + 3 * (m : ℝ) / 4)) ∧
      distProfile (dm m γ) γ = certWorkload (dm m γ) γ / infoWorkload (dm m γ) γ ∧
      certWorkload (dm m γ) γ / infoWorkload (dm m γ) γ = 1 + 3 / 8 * Real.logb 2 ((4 : ℝ) ^ m) ∧
      c * (1 + Real.log (γ ^ 2 * infoWorkload (dm m γ) γ)) ≤ distProfile (dm m γ) γ ∧
      distProfile (dm m γ) γ ≤ C * (1 + Real.log (γ ^ 2 * infoWorkload (dm m γ) γ)) ∧
      certWorkloadInt (dm m γ) γ = certWorkload (dm m γ) γ ∧
      ((∃ q : ℚ, (q : ℝ) = γ) → ∀ x y, ∃ q : ℚ, (q : ℝ) = dm m γ x y) := by sorry

end MetricMinTest
