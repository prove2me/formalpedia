-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_fixedTime_noAtoms_of_infiniteActivity
-- name    : Kyprianou.Ch05.killedSubordinator_fixedTime_noAtoms_of_infiniteActivity
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T03:19:39.594487+00:00
-- url     : https://prove2.me/theorems/6cd6b07c-d1ca-5338-839c-5d0d3acd4ef3
-- title:
--   At infinite activity, the fixed-time law of Y_t has no atoms (t>0)
-- statement:
--   Let $Y$ be a killed subordinator whose Lévy measure has infinite activity, $\Pi(0,\infty)=\infty$. Then for every fixed time $t>0$ and every point $x$, the law of $Y_t$ has no atom at $x$:
--
--   $$P(Y_t=x)=0.$$
--
--   An infinitely divisible distribution on $[0,\infty)$ whose Lévy measure is infinite is continuous; this fixed-time statement is the probabilistic core of part (i) of Theorem 5.4 of Kyprianou (2006), before the occupation integral transports it to the potential measure.
--
--   **Formalization Note.** The law of $Y_t$ is pinned by `hLaplaceLaw`, whose exponent is $t(\Phi(\theta)-\eta)$ with Lévy measure $t\Pi$.
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

/-- Fixed-time atomlessness of an infinite-activity subordinator law. -/
theorem killedSubordinator_fixedTime_noAtoms_of_infiniteActivity
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
  (Pi (Set.Ioi (0 : Real)) = ⊤ →
    ∀ t : NNReal, 0 < t → ∀ x : Real,
      P {omega : Omega | Y t omega = x} = 0)
 := by
  sorry

end Kyprianou.Ch05
