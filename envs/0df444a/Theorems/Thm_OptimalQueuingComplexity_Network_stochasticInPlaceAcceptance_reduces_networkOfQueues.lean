-- Prove2me | Theorems.Thm_OptimalQueuingComplexity_Network_stochasticInPlaceAcceptance_reduces_networkOfQueues
-- name    : OptimalQueuingComplexity.Network.stochasticInPlaceAcceptance_reduces_networkOfQueues
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T10:48:07.398854+00:00
-- url     : https://prove2.me/theorems/4ca65735-5ebe-4fb5-9ad7-5e9d3d393d56
-- title:
--   Theorem 1 (completeness) — STOCHASTIC IN-PLACE ACCEPTANCE reduces to NETWORK OF QUEUES
-- statement:
--   There is a polynomial-time computable map $f$ from STOCHASTIC IN-PLACE ACCEPTANCE instances to NETWORK OF QUEUES instances such that, for every instance $x = (M, n)$,
--   $$M \text{ accepts } 0^n \text{ in place} \iff f(x) \text{ is a yes-instance of NETWORK OF QUEUES}.$$
--   Computability is measured on the encodings: $n$ in unary on the input side, and the length-faithful binary instance encoding on the output side.
--
--   This is the completeness half of Theorem 1. Combined with Lemma 1 and the transitivity of polynomial-time reductions, it gives EXP-hardness of NETWORK OF QUEUES.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), pp. 296–300, proof of Theorem 1 (completeness)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Network_EXPComplete
import Definitions.Def_OptimalQueuingComplexity_Network_stochasticInPlaceAcceptance
import Definitions.Def_OptimalQueuingComplexity_Network_networkOfQueues

namespace OptimalQueuingComplexity.Network

/-- Theorem 1, completeness part (Papadimitriou & Tsitsiklis 1999, pp. 296–300): STOCHASTIC
IN-PLACE ACCEPTANCE polynomial-time many-one reduces to NETWORK OF QUEUES. -/
theorem stochasticInPlaceAcceptance_reduces_networkOfQueues :
    PolyReduces SIPAInstance.enc stochasticInPlaceAcceptance
      Instance.enc networkOfQueues := by sorry

end OptimalQueuingComplexity.Network
