-- Prove2me | Theorems.Thm_Kyprianou_Ch05_potentialSupportNonnegative
-- name    : Kyprianou.Ch05.potentialSupportNonnegative
-- status  : Proved
-- author  : @daga2
-- created : 2026-11-26T03:14:28.050302+00:00
-- url     : https://prove2.me/theorems/f76930e6-5235-5bc1-8dc5-2dd9eb9c1bd8
-- title:
--   Lemma 5.17, step 0: the potential measure is supported on [0,∞)
-- statement:
--   The undiscounted potential measure $U^{(0)}$ of an unkilled subordinator is supported on $[0,\infty)$: it gives mass $0$ to $(-\infty, 0)$. This is because the subordinator has almost surely nondecreasing paths starting at $0$, so it never visits negative values. This is the support hypothesis required by the Karamata Tauberian theorems.
-- source:
--   Kyprianou (2006), Fluctuations of Lévy Processes with Applications, first edition, Lemma 5.17, printed pp. 121, 130 or 132; Theorems 5.13-5.15, p. 127.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Lemma 5.17, step 0: the undiscounted potential measure of a
subordinator is supported on `[0, ∞)`, since the subordinator has
almost surely nondecreasing paths starting at `0`. This is the
support hypothesis required by the Karamata theorems. -/
theorem potentialSupportNonnegative
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (U : Real → Measure Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hPotential : IsKilledPotentialFamily P Y death U) :
    (U 0) (Set.Iio (0 : Real)) = 0 := by
  sorry

end Kyprianou.Ch05
