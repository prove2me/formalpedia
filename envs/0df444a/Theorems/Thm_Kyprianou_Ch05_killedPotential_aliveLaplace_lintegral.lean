-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_aliveLaplace_lintegral
-- name    : Kyprianou.Ch05.killedPotential_aliveLaplace_lintegral
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:19:38.717885+00:00
-- url     : https://prove2.me/theorems/89312598-6355-5224-92e5-ad76ea329e94
-- title:
--   Survival-restricted Laplace integral of Y_t equals exp(-t Phi(theta))
-- statement:
--   Let $Y$ be a subordinator killed at an independent exponential time of rate $\eta$, with exponent $\Phi$. For $t\ge 0$ and $\theta\ge 0$, the Laplace integral of $Y_t$ restricted to the survival event factors by independence of the killing time and the path:
--
--   $$\int_{\{t<\mathrm{death}\}} e^{-\theta Y_t}\,dP = e^{-\eta t}\,e^{-t(\Phi(\theta)-\eta)} = e^{-t\Phi(\theta)}.$$
--
--   This is the pointwise-in-$t$ input to the resolvent identity behind Theorem 5.4 of Kyprianou (2006).
--
--   **Formalization Note.** The unrestricted integral is `hLaplaceLaw`; the survival probability is the second component of `IsKilledSubordinator`, and independence is its third.
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

/-- Killing independence splits the survival-restricted Laplace integral. -/
theorem killedPotential_aliveLaplace_lintegral
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
  ∀ (t : Real), 0 ≤ t → ∀ theta : Real, 0 ≤ theta →
      (∫⁻ omega in {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega},
        ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P) =
      ENNReal.ofReal (Real.exp (-t * Phi theta))
 := by
  sorry

end Kyprianou.Ch05
