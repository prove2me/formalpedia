-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_atomless_of_fixedTime_noAtoms
-- name    : Kyprianou.Ch05.killedPotential_atomless_of_fixedTime_noAtoms
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T03:19:41.96802+00:00
-- url     : https://prove2.me/theorems/a998d74d-a6b2-4bd6-abf3-f860bb1c0a8b
-- title:
--   Potential atomlessness from fixed-time atomlessness (occupation glue)
-- statement:
--   Let $U^q$ be the $q$-potential of a killed subordinator, given by the exact occupation formula. If the fixed-time laws are atomless, $P(Y_t=x)=0$ for all $t>0$ and all $x$, then every potential is atomless:
--
--   $$U^q\{x\}=\int_0^\infty e^{-qt} P(\text{alive at }t,\ Y_t=x)\,dt=0,$$
--
--   because the integrand is bounded by $P(Y_t=x)=0$ for every $t>0$, and the single time $t=0$ has Lebesgue measure zero. This is the transport step of part (i) of Theorem 5.4 of Kyprianou (2006).
--
--   **Formalization Note.** Only `IsKilledPotentialFamily` is used; no hypothesis on $\Pi$ appears, the fixed-time input is an explicit antecedent.
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

/-- Occupation-integral glue: a.e.-time atomlessness implies potential atomlessness. -/
theorem killedPotential_atomless_of_fixedTime_noAtoms
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
  ((∀ t : NNReal, 0 < t → ∀ x : Real,
      P {omega : Omega | Y t omega = x} = 0) →
    ∀ q : Real, 0 ≤ q → ∀ x : Real, (U q) {x} = 0)
 := by
  sorry

end Kyprianou.Ch05
