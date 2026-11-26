-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_latticeSupport_reverse
-- name    : Kyprianou.Ch05.killedPotential_latticeSupport_reverse
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:19:46.5509+00:00
-- url     : https://prove2.me/theorems/a36a6c53-a245-5428-9cd5-5cb2826a417e
-- title:
--   Theorem 5.4(iii) reverse: lattice support of the restricted potential implies that of Pi
-- statement:
--   Let $Y$ be a killed subordinator with finite jump activity and zero drift, $d=0$, as in Theorem 5.4(iii) of Kyprianou (2006). If for some (equivalently every) $q\ge 0$ the $q$-potential restricted to $(0,\infty)$ is concentrated on a lattice $h\mathbb Z$, $h>0$, then the Lévy measure is concentrated on the same lattice:
--
--   $$U^q|_{{(0,\infty)}}\{{z:z\notin h\mathbb Z\}}=0\ \Longrightarrow\ \Pi\{{z:z\notin h\mathbb Z\}}=0.$$
--
--   At small times the potential is governed by the first jump, whose size distribution is $\Pi$ normalized, so no off-lattice jump mass can hide from $U^q$.
--
--   **Formalization Note.** This is one direction of the child `killedPotential_latticeSupport_iff`, with the same hypotheses.
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

/-- Reverse direction of Theorem 5.4(iii). -/
theorem killedPotential_latticeSupport_reverse
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
  (Pi (Set.Ioi (0 : Real)) < ⊤ → d = 0 →
    ∀ h : Real, 0 < h → ∀ q : Real, 0 ≤ q →
      ((U q).restrict (Set.Ioi (0 : Real))) {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 →
      Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0)
 := by
  sorry

end Kyprianou.Ch05
