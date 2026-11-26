-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_laplaceTransform
-- name    : Kyprianou.Ch05.killedPotential_laplaceTransform
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T03:10:14.955315+00:00
-- url     : https://prove2.me/theorems/7e175c5a-7aab-4ce3-aa78-1ac592437b5b
-- title:
--   Laplace transform of the killed q-potential: 1/(q + Phi)
-- statement:
--   Let $Y$ be a subordinator killed at an independent exponential time of rate $\eta\ge 0$, with Laplace exponent $\Phi$ and $q$-potential measures $U^q$ given by the exact discounted occupation formula. Then for every $q\ge 0$ and $\theta\ge 0$, the Laplace transform of the $q$-potential is the reciprocal of $q+\Phi(\theta)$:
--
--   $$
--   \int_{[0,\infty)} e^{-\theta x}\,U^q(dx)=\frac{1}{q+\Phi(\theta)},\n$$
--
--   read in the extended nonnegative reals, so the identity also holds at $q=\Phi(\theta)=0$, where both sides are $+\infty$. This is the resolvent identity behind Theorem 5.4 of Kyprianou (2006): Tonelli's theorem turns the occupation integral into $\int_0^\infty e^{-qt} e^{-\eta t} e^{-t(\Phi(\theta)-\eta)}dt$, using independence of the killing time and the path.
--
--   **Formalization Note.** The transform is a Lebesgue integral (`lintegral`) against $U^q$ itself; no support hypothesis is needed because the occupation formula already forces $U^q$ to vanish on $(-\infty,0)$.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.4, Section 5.1, printed pp. 114-115; component decomposition of Kyprianou.Ch05.killedSubordinatorPotentialLattice (theorem_id 931e3306-d573-44a6-a001-adf4e80d2053).

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

/-- Laplace transform of the exact killed q-potential occupation measure. -/
theorem killedPotential_laplaceTransform
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
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U q)) =
        (ENNReal.ofReal (q + Phi theta))⁻¹
 := by
  sorry

end Kyprianou.Ch05
