-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_expNeg_setLintegral
-- name    : Kyprianou.Ch05.killedPotential_expNeg_setLintegral
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:19:30.452111+00:00
-- url     : https://prove2.me/theorems/ab79734f-1e3c-46d0-ba95-3dcc84d0c4b7
-- title:
--   Set-lintegral of exp(-a t) over [0,infinity) is 1/a in ENNReal
-- statement:
--   For every real $a\ge 0$,
--
--   $$\int_0^\infty e^{-at}\,dt=\frac1a,$$
--
--   read in the extended nonnegative reals: at $a=0$ both sides are $+\infty$. This is the final evaluation step of the resolvent identity behind Theorem 5.4 of Kyprianou (2006).
--
--   **Formalization Note.** The integral is a Lebesgue `lintegral` of `ENNReal.ofReal (Real.exp (-a * t))` against Lebesgue measure on $[0,\infty)$.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.4, Section 5.1, printed pp. 114-115; decomposition of Kyprianou.Ch05.killedSubordinatorPotentialLattice (931e3306-d573-44a6-a001-adf4e80d2053) and its children.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Elementary exponential integral, in ENNReal form. -/
theorem killedPotential_expNeg_setLintegral
    (a : Real) (ha : 0 ≤ a) :
  (∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-a * t)) ∂volume) =
      (ENNReal.ofReal a)⁻¹
 := by
  sorry

end Kyprianou.Ch05
