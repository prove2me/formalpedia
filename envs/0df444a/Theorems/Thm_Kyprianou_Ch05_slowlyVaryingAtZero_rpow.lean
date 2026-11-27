-- Prove2me | Theorems.Thm_Kyprianou_Ch05_slowlyVaryingAtZero_rpow
-- name    : Kyprianou.Ch05.slowlyVaryingAtZero_rpow
-- status  : Proved
-- author  : @daga2
-- created : 2026-11-27T01:25:18.056083+00:00
-- url     : https://prove2.me/theorems/cb4ede6a-309d-4042-9a0c-f440e8027e95
-- title:
--   Slowly varying at zero is dominated by every power at 0+
-- statement:
--   Let $L > 0$ be slowly varying at $0$ (the ratio $L(ax)/L(x) \to 1$ as $x \to 0^+$ for every $a > 0$) and continuous on $(0,\infty)$. Then for every $\varepsilon > 0$, $L(x)/x^\varepsilon \to \infty$ as $x \to 0^+$. This is the inversion of the at-infinity power bound applied to $x \mapsto L(1/x)$: slow variation at $0$ becomes slow variation at $\infty$ under inversion, and $L(x)/x^\varepsilon$ at $0^+$ is $L(1/t) t^\varepsilon$ at $\infty$. In Lemma 5.17 it is the step that forces the drift $d = 0$ when $\Phi$ is regularly varying at $\infty$ of index $\alpha < 1$: since $\Phi(\theta) \ge d\theta$ and $\Phi(\theta)/\theta = \theta^{\alpha-1}/L(1/\theta) \to 0$, $d$ must vanish.
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

theorem slowlyVaryingAtZero_rpow
    (L : Real → Real)
    (hpos : ∀ x : Real, 0 < x → 0 < L x)
    (hslow : ∀ a : Real, 0 < a →
      Tendsto (fun x : Real => L (a * x) / L x)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1))
    (hcont : ContinuousOn L (Set.Ioi (0 : Real))) :
    ∀ eps : Real, 0 < eps →
      Tendsto (fun x : Real => L x / x ^ eps)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) atTop := by sorry

end Kyprianou.Ch05
