-- Prove2me | Theorems.Thm_OptimalQueuingComplexity_Network_networkOfQueues_inEXP
-- name    : OptimalQueuingComplexity.Network.networkOfQueues_inEXP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T10:38:44.662719+00:00
-- url     : https://prove2.me/theorems/7a724132-14f6-4bcb-b5e4-577f07974f6e
-- title:
--   Theorem 1 (upper bound) — NETWORK OF QUEUES is in EXP
-- statement:
--   NETWORK OF QUEUES, with the length-faithful binary encoding of instances, is in EXP. Some Turing machine decides, for every encoded instance $I$, whether $I$ is well formed and some admissible policy $\pi$ has $J^\pi > K$, within $2^{p(|\mathrm{enc}(I)|)}$ steps for a polynomial $p$:
--   $$\text{NETWORK OF QUEUES} \in \mathrm{EXP}.$$
--
--   This is the upper-bound half of Theorem 1. The problem is an average-reward Markov decision process whose number of states is exponential in the size of the data.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 296, proof of Theorem 1 (upper bound)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Network_EXPComplete
import Definitions.Def_OptimalQueuingComplexity_Network_networkOfQueues

namespace OptimalQueuingComplexity.Network

/-- Theorem 1, upper bound (Papadimitriou & Tsitsiklis 1999, p. 296): NETWORK OF QUEUES can be
decided in exponential time. -/
theorem networkOfQueues_inEXP : InEXP Instance.enc networkOfQueues := by sorry

end OptimalQueuingComplexity.Network
