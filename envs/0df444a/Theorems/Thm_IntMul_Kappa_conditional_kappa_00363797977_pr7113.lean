-- Prove2me | Theorems.Thm_IntMul_Kappa_conditional_kappa_00363797977_pr7113
-- name    : IntMul.Kappa.conditional_kappa_00363797977_pr7113
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-10T17:55:45.322911+00:00
-- url     : https://prove2.me/theorems/2237aca5-65a8-449b-9297-b13cb7a0af48
-- title:
--   Exact integer multiplication with saving κ = 0.00363797977
-- statement:
--   There exists one deterministic multitape Turing machine, with fixed finite alphabet and tape count, that correctly multiplies every pair of n-bit inputs for all n ≥ 1, with worst-case time O(n L(n)^(1−0.00363797977)), where L(n) = max(ceil(log₂ n), 1). This is the full bound with no assumed algorithmic or analytic framework. Its proof is Open.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/pull/7113 (head 07a76c5e2738882c0cb322278e56f6cae3c9885d); original framework: https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026

import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.Kappa

theorem conditional_kappa_00363797977_pr7113 : KappaBound (0.00363797977 : ℝ) := by
  sorry

end IntMul.Kappa
