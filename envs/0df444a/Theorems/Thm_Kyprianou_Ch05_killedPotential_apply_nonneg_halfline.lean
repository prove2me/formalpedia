-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_apply_nonneg_halfline
-- name    : Kyprianou.Ch05.killedPotential_apply_nonneg_halfline
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T03:49:17.368819+00:00
-- url     : https://prove2.me/theorems/4cdb2dbc-f14a-5d99-b465-f80485a1ed6f
-- title:
--   The killed q-potential gives no mass to the negative half-line
-- statement:
--   A subordinator starts at $0$ and has nondecreasing paths, so $Y_t\ge 0$ for all $t$ almost surely. Hence the discounted occupation measure of a killed subordinator puts no mass on the negative half-line: for every $q\ge 0$,
--
--   $$U^q((-\infty,0))=0.$$
--
--   This is the boundary fact that lets the reverse direction of Theorem 5.4(iii) of Kyprianou (2006) pass from the restricted potential $U^q|_{(0,\infty)}$ back to the full potential $U^q$: the off-lattice set does not contain $0$, so its part inside $(-\infty,0]$ is exactly its part inside $(-\infty,0)$.
--
--   **Formalization Note.** Nonnegativity of the paths comes from `IsKilledSubordinator`: the underlying process is a Levy process (`start_zero`) and is a.e. monotone (`IsSubordinator`).
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

/-- The killed q-potential charges nothing below zero. -/
theorem killedPotential_apply_nonneg_halfline
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
  ∀ q : Real, 0 ≤ q → (U q) (Set.Iio (0 : Real)) = 0
 := by
  sorry

end Kyprianou.Ch05
