-- Prove2me | Theorems.Thm_OAI_QuarticPowerFree_allDegrees
-- name    : OAI.QuarticPowerFree.allDegrees
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:13.429978+00:00
-- url     : https://prove2.me/theorems/2ca8f932-1a00-4324-ac3c-86ad019288c3
-- statement:
--   The theorem states that, for any integer polynomial f whose image in ℚ[x] is irreducible, has degree d = natDegree f at least 4, and is locally admissible at exponent k = d − 2, the density statement holds at exponent k. Local admissibility means that for every prime p, the number ρ(p^k) of residues a modulo p^k (a in 0,…,p^k−1) with p^k dividing f(a) is strictly less than p^k. The density statement says three things: the local factors 1 − ρ(p^k)/p^k, indexed by primes, form a multipliable family; their infinite product C is strictly positive; and the count of n in {1,…,⌊X⌋} for which f(n) is k-th-power-free (no prime p has p^k dividing f(n)) equals C·X up to an error that is o(X) as X → ∞, so the count is asymptotically C·X.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PowerFreeValues.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PowerFreeValues.lean; bytes 1111..1348
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_PowerFreeValues

namespace OAI

open Filter Asymptotics

open scoped Topology

namespace QuarticPowerFree

theorem allDegrees (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hdeglo : 4 ≤ f.natDegree)
    (hlocal : LocallyAdmissible f (f.natDegree - 2)) :
    DensityStatement f (f.natDegree - 2) := by
  sorry

end QuarticPowerFree
end OAI
