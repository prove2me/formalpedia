-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalTailEventKernel
-- name    : Kyprianou.Ch05.renewalTailEventKernel
-- status  : Proved
-- author  : @DAGA
-- created : 2026-11-26T03:06:12.218503+00:00
-- url     : https://prove2.me/theorems/75b902c2-33f2-4624-b814-20a3062c6e8a
-- title:
--   Lemma 5.5 step: joint tail event as a renewal convolution
-- statement:
--   For $x, u, y > 0$, the probability that the overshoot exceeds $u$ and the undershoot exceeds $y$ equals the renewal convolution $\int_{z \in [0, x]} g(x - z) \, dU(z)$, where $U$ is the renewal measure and $g(t) = F((t + u, \infty))$ for $t > y$, $0$ otherwise. This is the finite-level joint law applied with $A = (u, \infty)$ and $B = (y, x]$: almost surely the undershoot lies in $(0, x]$ and the overshoot is positive on the event in question, the inner $F$-integral over the crossing spacing collapses to the tail $F((x - z + u, \infty))$, and passing from the $[0, \infty]$-valued identity to real values is legitimate because $P$ is a probability measure. The result is exactly the convolution form consumed by the key renewal theorem.
-- source:
--   Kyprianou (2006), first edition, Lemma 5.5, printed pp.116-117, equation (5.5).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05
theorem renewalTailEventKernel
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat -> Omega -> Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x u y : Real) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    (P {omega : Omega |
      u < renewalOvershoot Z x omega ∧
      y < renewalUndershoot Z x omega}).toReal =
    ∫ z in Set.Icc (0 : Real) x,
      (if y < x - z then (F (Set.Ioi (x - z + u))).toReal else 0)
      ∂(renewalMeasure F) := by
  sorry
end Kyprianou.Ch05
