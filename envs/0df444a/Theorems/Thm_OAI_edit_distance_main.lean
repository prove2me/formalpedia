-- Prove2me | Theorems.Thm_OAI_edit_distance_main
-- name    : OAI.edit_distance_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:40.945099+00:00
-- url     : https://prove2.me/theorems/73558d1a-3242-41e1-a927-41f21a85de82
-- statement:
--   The theorem states that there exist real constants c>0 and C>0 and a threshold d₀ such that for every d≥d₀ the following hold, where exponentScale(c,d)=exp(c·√(log d·log log d)). Edit distance between lists is the minimum number of unit-cost insertions, deletions and single-letter substitutions turning one into the other. For a set X with a distance ρ, the distortion of an injective map f into ℓ¹(ℕ) (absolutely summable real sequences) is the supremum of ‖f(x)−f(y)‖/ρ(x,y) over distinct pairs times the supremum of ρ(x,y)/‖f(x)−f(y)‖, and leastDistortion is the infimum of this over all such injections. E(Alpha,d) is the least distortion for the set of words over Alpha of length at most d with edit distance. First, for every finite alphabet Alpha (in the given universe) with at least two letters, exponentScale(c,d) ≤ E(Alpha,d) ≤ exponentScale(C,d). Second, BinaryWitness(c,d) holds: there are n≤d and a finite nonempty set S of binary words, all of length n, whose least distortion under edit distance is at least exponentScale(c,d). Third, with alphabetSup(d) the supremum of E(Fin m,d) over all m≥2, exponentScale(c,d) ≤ alphabetSup(d) ≤ exponentScale(C,d). The proof is admitted with sorry in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditDistance.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditDistance.lean; bytes 2913..2984
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EditDistance

namespace OAI

universe u

theorem edit_distance_main : EditDistortion.MainClaim.{u} := by
  sorry

end OAI
