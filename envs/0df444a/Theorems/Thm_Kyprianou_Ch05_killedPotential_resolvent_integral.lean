-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_resolvent_integral
-- name    : Kyprianou.Ch05.killedPotential_resolvent_integral
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T03:19:35.071421+00:00
-- url     : https://prove2.me/theorems/8d2eb7c9-3e4f-50af-bed4-349d1745e57c
-- title:
--   Discounted time integral of exp(-t Phi(theta)) is 1/(q + Phi(theta))
-- statement:
--   For a killed subordinator with exponent $\Phi$, $q\ge 0$ and $\theta\ge 0$, the discounted time integral of the survival-restricted Laplace transform is the resolvent value
--
--   $$\int_0^\infty e^{-qt} e^{-t\Phi(\theta)}\,dt=\frac{1}{q+\Phi(\theta)},$$
--
--   read in the extended nonnegative reals, so it also holds at $q=\Phi(\theta)=0$ with value $+\infty$. Combined with the Tonelli form of the potential, this gives the Laplace transform of $U^q$ used in Theorem 5.4 of Kyprianou (2006).
--
--   **Formalization Note.** The left side keeps the survival-restricted inner integral unevaluated; the evaluation $e^{-t\Phi(\theta)}$ is the separate child `killedPotential_aliveLaplace_lintegral`.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.4, Section 5.1, printed pp. 114-115; decomposition of Kyprianou.Ch05.killedSubordinatorPotentialLattice (931e3306-d573-44a6-a001-adf4e80d2053) and its children.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- The resolvent integral, after the survival-Laplace evaluation. -/
theorem killedPotential_resolvent_integral
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
  ∀ q : Real, 0 ≤ q → ∀ theta : Real, 0 ≤ theta →
      (∫⁻ t in Set.Ici (0 : Real),
        ENNReal.ofReal (Real.exp (-q * t)) *
        ∫⁻ omega in {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega},
          ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P ∂volume) =
      (ENNReal.ofReal (q + Phi theta))⁻¹
 := by
  sorry

end Kyprianou.Ch05
