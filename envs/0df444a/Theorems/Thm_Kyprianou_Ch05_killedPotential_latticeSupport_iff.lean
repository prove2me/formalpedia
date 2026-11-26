-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_latticeSupport_iff
-- name    : Kyprianou.Ch05.killedPotential_latticeSupport_iff
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:10:11.77382+00:00
-- url     : https://prove2.me/theorems/46f9607b-69d0-5c17-86f2-e60471b39a2f
-- title:
--   Theorem 5.4(iii): lattice support of Pi and of the restricted q-potential coincide when d=0
-- statement:
--   Let $Y$ be a killed subordinator with Laplace triplet $(\eta, d, \Pi)$ and $q$-potentials $U^q$ as in Theorem 5.4 of Kyprianou (2006). Assume finite jump activity, $\Pi(0,\infty)<\infty$, and zero drift, $d=0$. Then for every $q\ge 0$ and every span $h>0$, the jump measure is concentrated on the lattice $h\mathbb Z$ if and only if the $q$-potential restricted to $(0,\infty)$ is concentrated on the same lattice:
--
--   $$
--   \Pi\{z : z\notin h\mathbb Z\}=0\iff U^q|_{(0,\infty)}\{z : z\notin h\mathbb Z\}=0.\n$$
--
--   This is part (iii) of Theorem 5.4, isolated as a child lemma. The zero-drift hypothesis is essential: with $d>0$ the continuous drift component spreads the potential off every lattice even when all jumps lie on it, which is why the printed source statement needs this correction.
--
--   **Formalization Note.** Concentration on $h\mathbb Z$ is stated as the off-lattice set $\{z : \forall n\in\mathbb Z,\ z\ne n h\}$ having measure zero.
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

/-- Theorem 5.4(iii), pp. 114-115, with the necessary drift restriction d=0 that the printed source omits. -/
theorem killedPotential_latticeSupport_iff
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
     d = 0 →
     ∀ q : Real, 0 ≤ q →
       ∀ h : Real, 0 < h →
         (Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 ↔
          ((U q).restrict (Set.Ioi (0 : Real)))
            {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0))
 := by
  sorry

end Kyprianou.Ch05
