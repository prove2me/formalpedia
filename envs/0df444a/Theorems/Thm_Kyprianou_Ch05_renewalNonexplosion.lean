-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalNonexplosion
-- name    : Kyprianou.Ch05.renewalNonexplosion
-- status  : Open
-- author  : @DAGA
-- created : 2026-11-26T03:06:12.868004+00:00
-- url     : https://prove2.me/theorems/b0a15864-6795-4781-a895-9882c40b1efb
-- title:
--   Lemma 5.5 step: renewal epochs do not explode
-- statement:
--   Under the renewal epoch process hypotheses with common spacing law $F$ satisfying $F(\{0\}) \neq 1$ (hence $F(\{0\}) < 1$, since $F$ is the law of a random variable under a probability measure), the renewal epochs $S_n$ tend to infinity almost surely. Consequently, for every level $x \ge 0$, the first index $N_x$ with $S_{N_x} > x$ is almost surely a genuine positive index: the degenerate fallback value $N_x = 0$, which the definition assigns when no epoch exceeds $x$, occurs only on a $P$-null set. The point is that some band $[\varepsilon, \infty)$ carries positive $F$-mass, so a positive fraction of spacings exceed $\varepsilon$ and the partial sums diverge.
-- source:
--   Kyprianou (2006), first edition, Lemma 5.5, printed pp.116-117, equation (5.5).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05
theorem renewalNonexplosion
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat -> Omega -> Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (x : Real) (hx : 0 <= x) :
    P {omega : Omega | nextRenewalIndex Z x omega = 0} = 0 := by
  sorry
end Kyprianou.Ch05
