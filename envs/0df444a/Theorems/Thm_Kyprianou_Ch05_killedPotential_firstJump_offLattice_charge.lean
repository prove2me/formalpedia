-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_firstJump_offLattice_charge
-- name    : Kyprianou.Ch05.killedPotential_firstJump_offLattice_charge
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:19:53.83463+00:00
-- url     : https://prove2.me/theorems/717cda54-49d3-5299-926d-190f0d836fa2
-- title:
--   First-jump transport: off-lattice Pi mass charges the potential off the lattice
-- statement:
--   Let $Y$ be a killed subordinator with finite jump activity, $\Pi(0,\infty)<\infty$, as in Theorem 5.4(ii) of Kyprianou (2006). Fix a span $h>0$. If the Lévy measure puts nonzero mass off the lattice $h\mathbb Z$, then every $q$-potential, $q\ge 0$, also puts nonzero mass off the same lattice:
--
--   $$\Pi\{{z:z\notin h\mathbb Z\}}\ne 0\ \Longrightarrow\ U^q\{{z:z\notin h\mathbb Z\}}\ne 0.$$
--
--   The mechanism is the first jump: with positive probability the first jump is an off-lattice jump, and after it the path spends positive expected discounted time at off-lattice positions, which the occupation formula records in $U^q$.
--
--   **Formalization Note.** This is exactly the content of `NonLatticeMeasure Pi → NonLatticeMeasure (U q)` after unfolding `NonLatticeMeasure`, isolated as the first-jump child of part (ii).
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

/-- First-jump decomposition step behind Theorem 5.4(ii). -/
theorem killedPotential_firstJump_offLattice_charge
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
  (Pi (Set.Ioi (0 : Real)) < ⊤ →
    ∀ h : Real, 0 < h → Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ≠ 0 →
      ∀ q : Real, 0 ≤ q → (U q) {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ≠ 0)
 := by
  sorry

end Kyprianou.Ch05
