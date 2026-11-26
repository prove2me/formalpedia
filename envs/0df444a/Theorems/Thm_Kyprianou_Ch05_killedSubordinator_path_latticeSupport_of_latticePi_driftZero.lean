-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_path_latticeSupport_of_latticePi_driftZero
-- name    : Kyprianou.Ch05.killedSubordinator_path_latticeSupport_of_latticePi_driftZero
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:21:10.979491+00:00
-- url     : https://prove2.me/theorems/f9896370-f672-540b-bd61-3f6048c6ed76
-- title:
--   Zero drift and lattice jump support put the whole path on the lattice a.s. (corrected, with d=0)
-- statement:
--   Let $Y$ be a subordinator with zero drift, $d=0$, whose Lévy measure $\Pi$ is concentrated on a lattice $h\mathbb Z$, $h>0$. Then at every time $t$, the path position lies on the same lattice almost surely:
--
--   $$Y_t\in h\mathbb Z\qquad P\text{-a.s.}$$
--
--   With no drift, $Y_t$ is a sum of jumps, and every jump lies in $h\mathbb Z$. This is the corrected form of the path-support child for part (iii) of Theorem 5.4 of Kyprianou (2006): the zero-drift hypothesis is essential, since a positive drift moves the path off every lattice between jumps.
--
--   **Formalization Note.** This corrects `killedSubordinator_path_latticeSupport_of_latticePi`, which omitted $d=0$ and is false as stated; that node is deprecated in favour of this one.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.4(iii), Section 5.1, printed pp. 114-115; corrected decomposition child.

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

/-- Path support on hZ when d=0 and Pi is concentrated on hZ. Corrected version with the essential d=0 hypothesis. -/
theorem killedSubordinator_path_latticeSupport_of_latticePi_driftZero
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
  (d = 0 → ∀ h : Real, 0 < h → Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 →
    ∀ t : NNReal, ∀ᵐ omega : Omega ∂P,
      ∃ n : Int, Y t omega = (n : Real) * h)
 := by
  sorry

end Kyprianou.Ch05
