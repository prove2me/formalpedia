-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalTailIntegralEq
-- name    : Kyprianou.Ch05.renewalTailIntegralEq
-- status  : Open
-- author  : @DAGA
-- created : 2026-11-26T03:06:03.070653+00:00
-- url     : https://prove2.me/theorems/ec42005c-e456-591c-ae1f-86ba44488219
-- title:
--   Lemma 5.5 step: integral of the truncated tail
-- statement:
--   For any measure $F$ on $\mathbb{R}$ and any reals $u, y$, the Lebesgue integral over $[0, \infty)$ of the truncated tail function $t \mapsto F((t + u, \infty)) \mathbf{1}\{t > y\}$ equals the integrated tail $\int_{u+y}^{\infty} F((s, \infty)) \, ds$. This is the translation substitution $s = t + u$, under which the condition $t > y$ becomes $s > u + y$; both sides are integrals of the same nonnegative measurable function after the shift, so the identity holds without any finiteness assumption, with the usual conventions for non-integrable functions.
-- source:
--   Kyprianou (2006), first edition, Lemma 5.5, printed pp.116-117, equation (5.5).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05
theorem renewalTailIntegralEq
    (F : Measure Real) (u y : Real) :
    (∫ z in Set.Ici (0 : Real),
      (if y < z then (F (Set.Ioi (z + u))).toReal else 0) ∂volume) =
    ∫ z in Set.Ioi (u + y), (F (Set.Ioi z)).toReal ∂volume := by
  sorry
end Kyprianou.Ch05
