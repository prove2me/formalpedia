-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedTailLaplaceTransform
-- name    : Kyprianou.Ch05.killedTailLaplaceTransform
-- status  : Proved
-- author  : @daga2
-- created : 2026-11-27T01:25:25.537538+00:00
-- url     : https://prove2.me/theorems/ef7a1762-bd50-4c00-8efb-34ab0be76d37
-- title:
--   Laplace transform of the Lévy tail density is (Φ(θ) − dθ)/θ
-- statement:
--   Let $\bar\Pi(x) = \Pi((x,\infty))$ be the tail of the Lévy measure of a killed subordinator with drift $d$ and Laplace exponent $\Phi$ (killing rate $0$). The Laplace transform of the density $\bar\Pi$ on $[0,\infty)$ is $(\Phi(\theta) - d\theta)/\theta$ for $\theta > 0$. This is the Tonelli computation $\int_0^\infty e^{-\theta y} \bar\Pi(y)\,dy = \int_0^\infty \int_0^x e^{-\theta y}\,dy\,\Pi(dx) = \int_0^\infty (1 - e^{-\theta x})/\theta\,\Pi(dx)$, and the source equation $\Phi(\theta) = d\theta + \int_0^\infty (1 - e^{-\theta x})\,\Pi(dx)$ identifies the last integral with $\Phi(\theta) - d\theta$. This is the analytic core of the tail half of Lemma 5.17.
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

theorem killedTailLaplaceTransform
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (theta : Real) (htheta : 0 < theta) :
    positiveLaplace
      (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
        (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal))) theta
      = ENNReal.ofReal ((Phi theta - d * theta) / theta) := by sorry

end Kyprianou.Ch05
