-- Prove2me | Theorems.Thm_Kyprianou_Ch05_potentialScalingLimits
-- name    : Kyprianou.Ch05.potentialScalingLimits
-- status  : Open
-- author  : @daga2
-- created : 2026-11-26T03:14:36.697239+00:00
-- url     : https://prove2.me/theorems/b6643f62-b02d-437b-9cb4-84c255af0d1b
-- title:
--   Karamata ratio to scaled potential limit, at both endpoints
-- statement:
--   A pure Karamata scaling step, with no probability in it. Let $U$ be a measure on $\mathbb{R}$, let $L$ be slowly varying, and let $\Phi(1/x) = x^{-\rho} L(x)$ for $x > 0$ with $\rho \ge 0$. If the cumulative ratio $U([0,x]) / (x^\rho L(x) / \Gamma(1+\rho))$ tends to $1$, then for every $\lambda > 0$ the scaled mass $U([0,\lambda x]) \cdot \Phi(1/x)$ tends to $\lambda^\rho / \Gamma(1+\rho)$. This holds both as $x \to \infty$ (with $L$ slowly varying at $\infty$) and as $x \to 0^+$ (with $L$ slowly varying at $0$). It is the final step converting the Karamata Tauberian conclusion into the potential-mass limit of Lemma 5.17.
-- source:
--   Kyprianou (2006), Fluctuations of Lévy Processes with Applications, first edition, Lemma 5.17, printed pp. 121, 130 or 132; Theorems 5.13-5.15, p. 127.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Pure Karamata scaling step for the potential: if the cumulative
ratio `U([0, x]) / (x ^ rho * L x / Gamma (1 + rho))` tends to `1`,
then for every `lambda > 0` the scaled mass
`U([0, lambda * x]) * Phi (1 / x)` tends to
`lambda ^ rho / Gamma (1 + rho)`, at both endpoints, where
`Phi (1 / x) = x ^ (-rho) * L x` and `L` is slowly varying at the
matching endpoint. -/
theorem potentialScalingLimits
    (U : Measure Real) (Phi L : Real → Real) (rho : Real)
    (hRho : 0 ≤ rho)
    (hPhi : ∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-rho) * L x) :
  ((SlowlyVaryingAtInfinity L →
     Tendsto
       (fun x : Real =>
         ((U) (Set.Icc (0 : Real) x)).toReal /
           (x ^ rho * L x / Real.Gamma (1 + rho)))
       atTop (nhds 1) →
     ∀ lambda : Real, 0 < lambda →
       Tendsto
         (fun x : Real =>
           ((U) (Set.Icc (0 : Real) (lambda * x))).toReal * Phi (1 / x))
         atTop (nhds (lambda ^ rho / Real.Gamma (1 + rho)))) ∧
   (SlowlyVaryingAtZero L →
     Tendsto
       (fun x : Real =>
         ((U) (Set.Icc (0 : Real) x)).toReal /
           (x ^ rho * L x / Real.Gamma (1 + rho)))
       (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) →
     ∀ lambda : Real, 0 < lambda →
       Tendsto
         (fun x : Real =>
           ((U) (Set.Icc (0 : Real) (lambda * x))).toReal * Phi (1 / x))
         (nhdsWithin (0 : Real) (Set.Ioi 0))
         (nhds (lambda ^ rho / Real.Gamma (1 + rho))))) := by
  sorry

end Kyprianou.Ch05
