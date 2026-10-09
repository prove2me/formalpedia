-- Prove2me | Theorems.Thm_IntMul_Kappa_community_pr62
-- name    : IntMul.Kappa.community_pr62
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-08T23:05:13.43562+00:00
-- url     : https://prove2.me/theorems/d39f627f-d682-442d-838f-d09ac76a0a08
-- title:
--   Full multiplication bound at κ = 0.000051016920170078
-- statement:
--   There exists one deterministic multitape Turing machine, with fixed finite alphabet and tape count, that correctly multiplies every pair of n-bit inputs for all n ≥ 1, with worst-case time O(n L(n)^(1−0.000051016920170078)), where L(n) = max(ceil(log₂ n), 1). This is the full bound with no assumed algorithmic or analytic framework. Its proof is Open.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/tree/56b66d58297deca1d7dd130247d720e960f77a37; original framework: https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026

import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.Kappa

theorem community_pr62 :
    KappaBound (0.000051016920170078 : ℝ) := by
  sorry

end IntMul.Kappa
