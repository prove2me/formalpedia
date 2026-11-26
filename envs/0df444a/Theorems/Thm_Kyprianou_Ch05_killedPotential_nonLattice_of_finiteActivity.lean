-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_nonLattice_of_finiteActivity
-- name    : Kyprianou.Ch05.killedPotential_nonLattice_of_finiteActivity
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:10:08.252749+00:00
-- url     : https://prove2.me/theorems/8f62c55d-ff58-54c3-bf78-e571bdc8edb5
-- title:
--   Theorem 5.4(ii): finite nonlattice jump support makes q-potentials nonlattice
-- statement:
--   Let $Y$ be a killed subordinator with Laplace triplet $(\eta, d, \Pi)$, exponent $\Phi$, and $q$-potential measures $U^q$ as in Theorem 5.4 of Kyprianou (2006). Assume finite jump activity, $\Pi(0,\infty)<\infty$, and assume $\Pi$ is nonlattice in the sense that for every span $h>0$ some of its mass lies off the lattice $h\mathbb Z$. Then every $q$-potential with $q\ge 0$ is also nonlattice:
--
--   $$
--   \forall h>0,\qquad U^q\{z : z\notin h\mathbb Z\}\ne 0.\n$$
--
--   This is part (ii) of Theorem 5.4, isolated as a child lemma: the potential measure cannot concentrate on a lattice that the jump measure itself escapes.
--
--   **Formalization Note.** Nonlattice is the predicate `NonLatticeMeasure`, stated with the off-lattice set $\{x : \forall n\in\mathbb Z,\ x\ne n h\}$ having nonzero measure.
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

/-- Theorem 5.4(ii), pp. 114-115: nonlattice inheritance by the q-potential. -/
theorem killedPotential_nonLattice_of_finiteActivity
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
     NonLatticeMeasure Pi →
     ∀ q : Real, 0 ≤ q → NonLatticeMeasure (U q))
 := by
  sorry

end Kyprianou.Ch05
