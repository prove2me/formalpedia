-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalTailDRI
-- name    : Kyprianou.Ch05.renewalTailDRI
-- status  : Proved
-- author  : @DAGA
-- created : 2026-11-26T03:06:06.186949+00:00
-- url     : https://prove2.me/theorems/c23004da-9a96-4025-9e16-f70def4f18c0
-- title:
--   Lemma 5.5 step: truncated spacing tail is directly Riemann integrable
-- statement:
--   Let $F$ be a probability measure on $[0, \infty)$ with finite mean, and fix $u, y > 0$. The function $g(t) = F((t + u, \infty))$ for $t > y$ and $g(t) = 0$ for $t \le y$ is directly Riemann integrable in the sense of the renewal-measure definitions: it is Lebesgue integrable (its integral is the integrated tail $\int_{u+y}^{\infty} F((s, \infty)) \, ds \le \mu$), bounded on every compact interval, and its grid upper-lower oscillation sums vanish with the mesh because $g$ is monotone nonincreasing on $(y, \infty)$ with a single jump at $y$. This is the test function to which the key renewal theorem is applied for the limiting joint tail.
-- source:
--   Kyprianou (2006), first edition, Lemma 5.5, printed pp.116-117, equation (5.5).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05
theorem renewalTailDRI
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hInt : Integrable (fun z : Real => z) F)
    (u y : Real) (hu : 0 < u) (hy : 0 < y) :
    DirectlyRiemannIntegrable
      (fun t : Real => if y < t then (F (Set.Ioi (t + u))).toReal else 0) := by
  sorry
end Kyprianou.Ch05
