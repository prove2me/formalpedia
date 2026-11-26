-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_latticeSupport_of_pathSupport
-- name    : Kyprianou.Ch05.killedPotential_latticeSupport_of_pathSupport
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T03:19:40.267871+00:00
-- url     : https://prove2.me/theorems/57f66e91-ec65-4642-b250-abca705efe88
-- title:
--   Restricted potential lattice support from path lattice support (occupation glue)
-- statement:
--   Let $U^q$ be the $q$-potential of a killed subordinator, given by the exact occupation formula, and fix a span $h>0$. If at every time $t$ the path position almost surely avoids the off-lattice set $\{{z:\forall n,\ z\ne nh\}}$, then the potential restricted to $(0,\infty)$ also avoids it:
--
--   $$U^q|_{{(0,\infty)}}\{{z:z\notin h\mathbb Z\}}=\int_0^\infty e^{-qt}P(\text{alive at }t,\ Y_t\notin h\mathbb Z,\ Y_t>0)\,dt=0.$$
--
--   This is the transport step of the forward half of part (iii) of Theorem 5.4 of Kyprianou (2006).
--
--   **Formalization Note.** Only `IsKilledPotentialFamily` and the restriction formula for measures are used; the path input is an explicit antecedent for every $t$, including $t=0$.
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

/-- Occupation-integral glue: path lattice support implies potential lattice support. -/
theorem killedPotential_latticeSupport_of_pathSupport
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
  (∀ h : Real, 0 < h →
    (∀ t : NNReal, P {omega : Omega | Y t omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} = 0) →
    ∀ q : Real, 0 ≤ q →
      ((U q).restrict (Set.Ioi (0 : Real))) {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0)
 := by
  sorry

end Kyprianou.Ch05
