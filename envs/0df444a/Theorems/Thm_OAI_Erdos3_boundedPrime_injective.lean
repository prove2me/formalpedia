-- Prove2me | Theorems.Thm_OAI_Erdos3_boundedPrime_injective
-- name    : OAI.Erdos3.boundedPrime_injective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T15:24:09.466832+00:00
-- url     : https://prove2.me/theorems/870602d1-d12a-4ac3-980e-a52db5a88046
-- title:
--   The value map on primes at most Q is injective
-- statement:
--   For every natural number $Q$, the map `boundedPrime Q` is injective. Here `BoundedPrime Q` is the subtype of elements of `boundedPrimes Q`, the finite set of primes $p\le Q$, and `boundedPrime Q p` is the underlying natural number of such an element $p$.
--
--   Lean: `OAI.Erdos3.boundedPrime_injective` in `lean/OAI/Combinatorics/Progressions/Lattices/BoundedPrimeDepthBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B094` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/BoundedPrimeDepthBudget.lean#L33

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_OAIErdos3B094

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boundedPrime_injective (Q : ℕ) : Function.Injective (boundedPrime Q) := by
  sorry

end Erdos3
end
end OAI
