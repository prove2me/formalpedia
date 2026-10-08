-- Prove2me | Theorems.Thm_OAI_GaussianMoat_fullMain
-- name    : OAI.GaussianMoat.fullMain
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:42.111274+00:00
-- url     : https://prove2.me/theorems/5d9f68f2-ff37-4c86-989b-6ead79213308
-- statement:
--   The theorem states that both of two Gaussian-moat endpoint propositions hold. The first, MainEndpoint, says that for every real step bound D there is no sequence z : ℕ → ℤ[i] of Gaussian integers such that every z(t) is irreducible (a Gaussian prime), z is injective, and consecutive terms satisfy |z(t+1) − z(t)| ≤ D in the complex plane; that is, no infinite walk through distinct Gaussian primes with steps of length at most D exists. The second, UniformEndpoint, says that for every real D there is a natural number B such that two things hold. First, in the graph whose vertices are the Gaussian primes and in which two distinct primes are adjacent when their complex distance is at most D, every connected component is finite and has at most B elements. Second, for every n and every injective list z₀, …, z_{n−1} of Gaussian primes whose consecutive entries are at distance at most D, the length n is at most B.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianMoat.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianMoat.lean; bytes 1073..1138
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_GaussianMoat

namespace OAI

namespace GaussianMoat

theorem fullMain : MainEndpoint ∧ UniformEndpoint := by
  sorry

end GaussianMoat
end OAI
