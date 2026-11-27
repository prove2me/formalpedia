-- Prove2me | Theorems.Thm_Kyprianou_Ch05_tailScalingFilter
-- name    : Kyprianou.Ch05.tailScalingFilter
-- status  : Proved
-- author  : @daga2
-- created : 2026-11-27T00:47:56.758743+00:00
-- url     : https://prove2.me/theorems/27b6c9e4-d71c-5ca7-b867-d038ec73dcd3
-- title:
--   Karamata tail scaling at a general positive endpoint filter
-- statement:
--   A pure Karamata scaling step, with no probability in it. Let $\Pi$ be a measure on $\mathbb{R}$, let $L$ be slowly varying, and let $\Phi(1/x) = x^{-\alpha} L(x)$ for $x > 0$ with $\alpha < 1$. If the density ratio $\Pi((x,\infty)) / (x^{-\alpha} L(x) / \Gamma(1-\alpha))$ tends to $1$ along a filter $l$ of positive $x$, then for every $a > 0$ the scaled tail $\Pi((a x,\infty)) / \Phi(1/x)$ tends to $a^{-\alpha} / \Gamma(1-\alpha)$ along $l$, whenever $x \mapsto a x$ preserves $l$ and $L(a x)/L(x) \to 1$ along $l$. This is the filter-generic form of the tail scaling step of Lemma 5.17, mirroring the proved potential scaling filter, with division by $\Phi$ in place of multiplication.
-- source:
--   Kyprianou (2006), Lemma 5.17 and Karamata's theorem, corrected reciprocal factor.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

namespace Kyprianou.Ch05

/-- Karamata tail scaling at a general positive endpoint filter: if the
density ratio `Pi((x, ∞)) / (x ^ (-alpha) * L x / Gamma (1 - alpha))`
tends to `1`, then for every `lambda > 0` the scaled tail
`Pi((lambda * x, ∞)) / Phi (1 / x)` tends to
`lambda ^ (-alpha) / Gamma (1 - alpha)`, where
`Phi (1 / x) = x ^ (-alpha) * L x` and `L` is slowly varying at the
matching endpoint. Mirror of `potentialScalingFilter` (WillR), with
division by `Phi` in place of multiplication. -/
theorem tailScalingFilter
    (Pi : Measure Real) (Phi L : Real → Real) (alpha : Real)
    (l : Filter Real) (hAlpha1 : alpha < 1)
    (hpos : ∀ᶠ x in l, 0 < x)
    (hL : ∀ x : Real, 0 < x → 0 < L x)
    (hPhi : ∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) * L x)
    (hDens : Tendsto (fun x : Real => (Pi (Set.Ioi x)).toReal /
      (x ^ ((1 - alpha) - 1) * L x / Real.Gamma (1 - alpha))) l (nhds 1))
    (a : Real) (ha : 0 < a)
    (hScale : Tendsto (fun x : Real => a * x) l l)
    (hSlow : Tendsto (fun x : Real => L (a * x) / L x) l (nhds 1)) :
    Tendsto (fun x : Real => (Pi (Set.Ioi (a * x))).toReal / Phi (1 / x)) l
      (nhds (a ^ (-alpha) / Real.Gamma (1 - alpha))) := by
  sorry

end Kyprianou.Ch05
