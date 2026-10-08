-- Prove2me | Theorems.Thm_MaxPressure_ReversedLeontief_extremeAllocs_eq_intAllocs
-- name    : MaxPressure.ReversedLeontief.extremeAllocs_eq_intAllocs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:07:01.640268+00:00
-- url     : https://prove2.me/theorems/d1fc6a02-74d4-4693-a831-dd2615cad3c8
-- title:
--   Lemma 1, p. 207 — in a reversed Leontief network, $\mathcal E=\mathcal N$
-- statement:
--   A stochastic processing network is reversed Leontief if each activity requires exactly one processor. For a reversed Leontief network satisfying the standing assumptions of §2, every extreme allocation is an integer allocation, and conversely:
--   $$\mathcal E=\mathcal N.$$
--
--   Consequently, maximum pressure policies in reversed Leontief networks never split a processor's capacity, and the throughput optimality of maximum pressure policies (Theorem 2 of the paper) carries over to the non-processor-splitting setting.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 207, Lemma 1 (proof p. 215, Appendix B)

import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network

namespace MaxPressure.ReversedLeontief

/-- Lemma 1, p. 207: for a reversed Leontief network, every extreme allocation is an integer
allocation; i.e., `ℰ = 𝒩`. -/
theorem extremeAllocs_eq_intAllocs {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) :
    extremeAllocs N = intAllocs N := by sorry

end MaxPressure.ReversedLeontief
