-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalMeanPos
-- name    : Kyprianou.Ch05.renewalMeanPos
-- status  : Open
-- author  : @DAGA
-- created : 2026-11-26T03:06:12.442005+00:00
-- url     : https://prove2.me/theorems/e6f014f8-6e38-4d73-9c97-c6111b122ac2
-- title:
--   Lemma 5.5 step: finite renewal mean is positive
-- statement:
--   If the spacings form a renewal epoch process with common law $F$ and the identity function is $F$-integrable, then the mean spacing $\mu = \int z \, dF(z)$ is strictly positive. Indeed $F$ is a probability measure supported on $[0, \infty)$ and $F(\{0\}) \neq 1$, so $F$ is not the Dirac mass at $0$; a nonnegative integrable random variable with expectation $0$ would be almost surely $0$, forcing $F = \delta_0$, a contradiction. Hence $\mu > 0$, which is the nondegeneracy the key renewal theorem requires.
-- source:
--   Kyprianou (2006), first edition, Lemma 5.5, printed pp.116-117, equation (5.5).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05
theorem renewalMeanPos
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat -> Omega -> Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (hInt : Integrable (fun z : Real => z) F) :
    0 < ∫ z : Real, z ∂F := by
  sorry
end Kyprianou.Ch05
