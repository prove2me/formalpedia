-- Prove2me | Theorems.Thm_Kyprianou_Ch05_tailScalingLimits
-- name    : Kyprianou.Ch05.tailScalingLimits
-- status  : Open
-- author  : @daga2
-- created : 2026-11-26T03:14:30.869688+00:00
-- url     : https://prove2.me/theorems/5608d87a-95f6-5b7c-b4ea-2f334c6baca5
-- title:
--   Karamata density ratio to scaled tail limit, at both endpoints
-- statement:
--   A pure Karamata scaling step, with no probability in it. Let $\Pi$ be a measure on $\mathbb{R}$, let $L$ be slowly varying, and let $\Phi(1/x) = x^{-\alpha} L(x)$ for $x > 0$ with $\alpha < 1$. If the density ratio $\Pi((x,\infty)) / (x^{-\alpha} L(x) / \Gamma(1-\alpha))$ tends to $1$, then for every $\lambda > 0$ the scaled tail $\Pi((\lambda x,\infty)) / \Phi(1/x)$ tends to $\lambda^{-\alpha} / \Gamma(1-\alpha)$. This holds both as $x \to \infty$ (with $L$ slowly varying at $\infty$) and as $x \to 0^+$ (with $L$ slowly varying at $0$). It is the final step converting the Karamata monotone-density conclusion into the Lévy-tail limit of Lemma 5.17.
-- source:
--   Kyprianou (2006), Fluctuations of Lévy Processes with Applications, first edition, Lemma 5.17, printed pp. 121, 130 or 132; Theorems 5.13-5.15, p. 127.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Pure Karamata scaling step for the tail: if the density ratio
`Pi((x, ∞)) / (x ^ (-alpha) * L x / Gamma (1 - alpha))` tends to `1`,
then for every `lambda > 0` the scaled tail
`Pi((lambda * x, ∞)) / Phi (1 / x)` tends to
`lambda ^ (-alpha) / Gamma (1 - alpha)`, at both endpoints, where
`Phi (1 / x) = x ^ (-alpha) * L x` and `L` is slowly varying at the
matching endpoint. Requires `alpha < 1` so `1 - alpha > 0`. -/
theorem tailScalingLimits
    (Pi : Measure Real) (Phi L : Real → Real) (alpha : Real)
    (hAlpha1 : alpha < 1)
    (hPhi : ∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) * L x) :
  ((SlowlyVaryingAtInfinity L →
     Tendsto
       (fun x : Real =>
         (Pi (Set.Ioi x)).toReal /
           (x ^ ((1 - alpha) - 1) * L x / Real.Gamma (1 - alpha)))
       atTop (nhds 1) →
     ∀ lambda : Real, 0 < lambda →
       Tendsto
         (fun x : Real =>
           (Pi (Set.Ioi (lambda * x))).toReal / Phi (1 / x))
         atTop (nhds (lambda ^ (-alpha) / Real.Gamma (1 - alpha)))) ∧
   (SlowlyVaryingAtZero L →
     Tendsto
       (fun x : Real =>
         (Pi (Set.Ioi x)).toReal /
           (x ^ ((1 - alpha) - 1) * L x / Real.Gamma (1 - alpha)))
       (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) →
     ∀ lambda : Real, 0 < lambda →
       Tendsto
         (fun x : Real =>
           (Pi (Set.Ioi (lambda * x))).toReal / Phi (1 / x))
         (nhdsWithin (0 : Real) (Set.Ioi 0))
         (nhds (lambda ^ (-alpha) / Real.Gamma (1 - alpha))))) := by
  sorry

end Kyprianou.Ch05
