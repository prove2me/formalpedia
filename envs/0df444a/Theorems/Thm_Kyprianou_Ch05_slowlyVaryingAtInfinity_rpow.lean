-- Prove2me | Theorems.Thm_Kyprianou_Ch05_slowlyVaryingAtInfinity_rpow
-- name    : Kyprianou.Ch05.slowlyVaryingAtInfinity_rpow
-- status  : Open
-- author  : @daga2
-- created : 2026-11-27T01:25:15.26498+00:00
-- url     : https://prove2.me/theorems/0ea57c0f-21d4-5ac3-8887-d85aca6264f9
-- title:
--   Slowly varying at infinity is dominated by every power
-- statement:
--   Let $L > 0$ be slowly varying at $\infty$ (the ratio $L(ax)/L(x) \to 1$ for every $a > 0$) and continuous on $(0,\infty)$. Then for every $\varepsilon > 0$, $L(x)/x^\varepsilon \to 0$ and $L(x) x^\varepsilon \to \infty$ as $x \to \infty$. The proof is the dyadic comparison: the ratio bound at $a = 2$ gives $L(2y) \le (1+\delta) L(y)$ eventually, and continuity bounds $L$ on one dyadic block $[X, 2X]$; iterating gives $L(x) \le C (x/X)^{\log_2(1+\delta)}$ with $\log_2(1+\delta) < \varepsilon$ for small $\delta$, and the symmetric lower bound with $1-\delta$. Continuity (hence boundedness on compacts) is essential: the ratio property alone does not imply the conclusion. This is the Karamata fact that makes the drift term negligible in the tail Laplace asymptotics of Lemma 5.17.
-- source:
--   Kyprianou (2006), Fluctuations of Lévy Processes with Applications, first edition, Lemma 5.17, printed pp. 121, 130 or 132; Theorems 5.13-5.15, p. 127.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

theorem slowlyVaryingAtInfinity_rpow
    (L : Real → Real)
    (hpos : ∀ x : Real, 0 < x → 0 < L x)
    (hslow : ∀ a : Real, 0 < a →
      Tendsto (fun x : Real => L (a * x) / L x) atTop (nhds 1))
    (hcont : ContinuousOn L (Set.Ioi (0 : Real))) :
    ∀ eps : Real, 0 < eps →
      Tendsto (fun x : Real => L x / x ^ eps) atTop (nhds 0) ∧
      Tendsto (fun x : Real => L x * x ^ eps) atTop atTop := by sorry

end Kyprianou.Ch05
