-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedLaplaceExponentDivTendstoAtZero
-- name    : Kyprianou.Ch05.killedLaplaceExponentDivTendstoAtZero
-- status  : Proved
-- author  : @daga2
-- created : 2026-11-27T01:25:21.382032+00:00
-- url     : https://prove2.me/theorems/0b4541a8-5e67-4341-9c51-8fab6872090d
-- title:
--   Regular variation at 0 of index < 1 forces Φ(θ)/θ → ∞
-- statement:
--   Let $\Phi$ be the Laplace exponent of a killed subordinator (killing rate $0$) with drift $d$, regularly varying at $0$ of index $\alpha < 1$. Then $\Phi(\theta)/\theta \to \infty$ as $\theta \to 0^+$. Otherwise $\int_0^\infty x\,\Pi(dx) < \infty$, and monotone convergence $(1 - e^{-\theta x})/\theta \uparrow x$ would give $\Phi(\theta)/\theta \to d + \int_0^\infty x\,\Pi(dx)$, a finite positive constant, so $\Phi(\lambda\theta)/\Phi(\theta) \to \lambda$ — regular variation of index $1$, contradicting index $\alpha < 1$ at $\lambda = 2$. Hence the drift term $d\theta$ is $o(\Phi(\theta))$ at $0$, which is what makes the tail Laplace ratio tend to $1$ in the at-zero half of Lemma 5.17.
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

theorem killedLaplaceExponentDivTendstoAtZero
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (alpha : Real) (hAlpha : 0 ≤ alpha ∧ alpha ≤ 1) (hAlpha1 : alpha < 1)
    (hRV : RegularlyVaryingAtZero Phi alpha) :
    Tendsto (fun theta : Real => Phi theta / theta)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) atTop := by sorry

end Kyprianou.Ch05
