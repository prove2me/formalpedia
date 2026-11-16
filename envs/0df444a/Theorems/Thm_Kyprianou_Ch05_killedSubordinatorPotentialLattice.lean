-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinatorPotentialLattice
-- name    : Kyprianou.Ch05.killedSubordinatorPotentialLattice
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:49:21.216543+00:00
-- url     : https://prove2.me/theorems/931e3306-d573-44a6-a001-adf4e80d2053
-- title:
--   Theorem 5.4: potential atoms and lattice support in three cases
-- statement:
--   Infinite jump activity makes q-potential measures atomless; finite nonlattice jump support makes U^(q) nonlattice; finite lattice jump support gives equivalent lattice supports for U^(q) on (0,infinity) when drift d=0. Original (iii) omits that necessary restriction, see source_issues_v1.md and drifted Poisson counterexample.
-- source:
--   Kyprianou (2006), first edition, numbered result 5.4, Section 5.1, printed pp. 113-115.

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

/-- Theorem 5.4, pp. 114-115: potential atoms and lattice support.
The printed part (iii) requires d=0, omitted in the source. -/
theorem killedSubordinatorPotentialLattice
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
  ((Pi (Set.Ioi (0 : Real)) = ⊤ →
    ∀ q : Real, 0 ≤ q →
      ∀ x : Real, (U q) {x} = 0) ∧
   (Pi (Set.Ioi (0 : Real)) < ⊤ →
     NonLatticeMeasure Pi →
     ∀ q : Real, 0 ≤ q → NonLatticeMeasure (U q)) ∧
   (Pi (Set.Ioi (0 : Real)) < ⊤ →
     d = 0 →
     ∀ q : Real, 0 ≤ q →
       ∀ h : Real, 0 < h →
         (Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 ↔
          ((U q).restrict (Set.Ioi (0 : Real)))
            {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0)))
 := by
  sorry

end Kyprianou.Ch05
