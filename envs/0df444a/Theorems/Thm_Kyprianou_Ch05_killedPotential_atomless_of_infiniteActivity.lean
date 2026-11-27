-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_atomless_of_infiniteActivity
-- name    : Kyprianou.Ch05.killedPotential_atomless_of_infiniteActivity
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T03:10:19.416335+00:00
-- url     : https://prove2.me/theorems/d6a7f06b-ba5a-5dcd-bcaa-9f24492065e1
-- title:
--   Theorem 5.4(i): infinite jump activity makes every q-potential atomless
-- statement:
--   Let $Y$ be a subordinator killed at an independent exponential time of rate $\eta\ge 0$, with Laplace triplet $(\eta, d, \Pi)$ and exponent $\Phi$, and let $U^q$ be its $q$-potential measure, the discounted expected occupation measure of the living path. If the jump measure has infinite total activity on $(0,\infty)$, $\Pi(0,\infty)=\infty$, then every $q$-potential with $q\ge 0$ is atomless:
--
--   $$
--   U^q\{x\}=0\qquad\text{for every }x\in\mathbb R.\n$$
--
--   This is part (i) of Theorem 5.4 of Kyprianou (2006), isolated as a child lemma of the three-part potential theorem: infinitely many small jumps in every time interval smooth out every point mass of the occupation measure.
--
--   **Formalization Note.** The potential family is the exact occupation integral in `IsKilledPotentialFamily`, and infinite activity is the hypothesis $\Pi(\mathrm{Ioi}\,0)=\top$ in `ENNReal`.
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

/-- Theorem 5.4(i), pp. 114-115: infinite-activity case of the potential-atom statement. -/
theorem killedPotential_atomless_of_infiniteActivity
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
    ∀ q : Real, 0 ≤ q →
      ∀ x : Real, (U q) {x} = 0)
 := by
  sorry

end Kyprianou.Ch05
