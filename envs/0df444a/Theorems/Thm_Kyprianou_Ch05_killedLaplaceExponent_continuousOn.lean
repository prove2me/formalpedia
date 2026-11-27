-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedLaplaceExponent_continuousOn
-- name    : Kyprianou.Ch05.killedLaplaceExponent_continuousOn
-- status  : Open
-- author  : @daga2
-- created : 2026-11-27T01:25:20.151804+00:00
-- url     : https://prove2.me/theorems/8db0cd15-5acf-457b-ba5a-7fe3ba6dc735
-- title:
--   Laplace exponent of a killed subordinator is continuous on [0,∞)
-- statement:
--   For a killed subordinator with Laplace triplet $(\eta, d, \Pi)$ and exponent $\Phi$, the source equation $\Phi(\theta) = \eta + d\theta + \int_0^\infty (1 - e^{-\theta x})\,\Pi(dx)$ for $\theta \ge 0$ makes $\Phi$ continuous on $[0,\infty)$: the drift term is linear and the integral term is continuous by dominated convergence, dominated by $\min(1, x)$ on any bounded $\theta$-interval, which is $\Pi$-integrable by the finite-variation hypothesis. This continuity is the regularity input that lets the slowly-varying factor $L(x) = x^{-\alpha}/\Phi(1/x)$ be bounded on compact intervals, which the Karamata power-bounds lemma needs.
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

theorem killedLaplaceExponent_continuousOn
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi) :
    ContinuousOn Phi (Set.Ici (0 : Real)) := by sorry

end Kyprianou.Ch05
