-- Prove2me | Theorems.Thm_Kyprianou_Ch05_potentialLaplaceAsymptotics
-- name    : Kyprianou.Ch05.potentialLaplaceAsymptotics
-- status  : Open
-- author  : @daga2
-- created : 2026-11-26T03:14:30.442391+00:00
-- url     : https://prove2.me/theorems/f9a82525-98d9-544c-8cde-47f2f683b692
-- title:
--   Lemma 5.17, step 1: Laplace asymptotics of the potential measure
-- statement:
--   For an unkilled subordinator with Laplace exponent $\Phi$ and undiscounted potential measure $U^{(0)}$, the Laplace transform of $U^{(0)}$ is $1/\Phi$. If $\Phi$ is regularly varying of index $\alpha \in [0,1]$, then this Laplace transform has the Karamata form: with the slowly varying factor $L$ determined by $\Phi$, the ratio of the Laplace transform to $\theta^{-\alpha} L(1/\theta)$ tends to $1$, as $\theta \to 0^+$ when $\Phi$ is regularly varying at $0$, and as $\theta \to \infty$ when $\Phi$ is regularly varying at $\infty$. The factor $L$ also satisfies $\Phi(1/x) = x^{-\alpha} L(x)$ for $x > 0$.
--
--   This is the analytic input that the Karamata Tauberian theorems (Theorems 5.13 and 5.15) convert into the potential-mass limits of Lemma 5.17.
--
--   **Formalization Note** The slowly varying factor is packaged existentially: the statement asserts the existence of an $L$ with the stated slow variation, the $\Phi$-link, and the Laplace asymptotic, rather than fixing a formula for $L$.
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

/-- Lemma 5.17, step 1 (potential): the Laplace transform of the
undiscounted potential measure is `1 / Phi`, and regular variation of
`Phi` transports to a Karamata-ready Laplace asymptotic, at both
endpoints. The slowly varying factor `L` is the one determined by
`Phi`, i.e. `L s = s ^ alpha * Phi (1 / s)`. -/
theorem potentialLaplaceAsymptotics
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (alpha : Real) (hAlpha : 0 ≤ alpha ∧ alpha ≤ 1) :
  ((RegularlyVaryingAtZero Phi alpha →
     ∃ L : Real → Real, SlowlyVaryingAtInfinity L ∧
       (∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) * L x) ∧
       Tendsto
         (fun theta : Real =>
           (positiveLaplace (U 0) theta).toReal /
             (theta ^ (-alpha) * L (1 / theta)))
         (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ∧
   (RegularlyVaryingAtInfinity Phi alpha →
     ∃ L : Real → Real, SlowlyVaryingAtZero L ∧
       (∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) * L x) ∧
       Tendsto
         (fun theta : Real =>
           (positiveLaplace (U 0) theta).toReal /
             (theta ^ (-alpha) * L (1 / theta)))
         atTop (nhds 1))) := by
  sorry

end Kyprianou.Ch05
