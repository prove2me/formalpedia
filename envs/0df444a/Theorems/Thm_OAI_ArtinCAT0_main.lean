-- Prove2me | Theorems.Thm_OAI_ArtinCAT0_main
-- name    : OAI.ArtinCAT0.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:21.320176+00:00
-- url     : https://prove2.me/theorems/9409c476-0f91-4dae-ba05-d05fc0607e7c
-- statement:
--   The theorem states that the following explicit matrix on 116 generators is symmetric, has diagonal entries 1, and has every off-diagonal entry in {2, 3, ∞}, and that its Artin group admits no geometric action on any nonempty proper CAT(0) metric space. Index the generators by 0, …, 115. For each b = 0, 1, 2, form the ordered block (b, (b + 1) mod 3, 5 + 37b, …, 41 + 37b). Distinct generators have matrix entry 3 if they are consecutive in a block; otherwise they have entry 2 if they are nonconsecutive members of a block or one is 3 or 4 and the other is 0, 1, or 2; all remaining entries are ∞. The Artin group has these generators and, for each finite entry n, equates the two alternating words of length n starting with the corresponding generators. Here a CAT(0) space is a geodesic metric space satisfying Euclidean triangle comparison, and proper means that closed balls are compact. The excluded geometric action is an action by isometries such that, for every compact set K, only finitely many group elements g satisfy gK ∩ K ≠ ∅, and some compact set has translates covering the whole space. Thus, for every nonempty proper metric space and every action of this explicitly presented group, at least one of the CAT(0), isometry, compact-intersection finiteness, or compact-covering conditions fails.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ArtinCAT0.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ArtinCAT0.lean; bytes 2370..2815
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ArtinCAT0

namespace OAI

namespace ArtinCAT0

universe uS uG uX

universe u

theorem main :
    (∀ s t : Letters, explicitMatrix s t = explicitMatrix t s) ∧
    (∀ s : Letters, explicitMatrix s s = 1) ∧
    (∀ s t : Letters, s ≠ t →
      explicitMatrix s t = 2 ∨ explicitMatrix s t = 3 ∨ explicitMatrix s t = ⊤) ∧
    (∀ (X : Type u) [MetricSpace X] [ProperSpace X] [Nonempty X]
      [MulAction (ArtinGroup explicitMatrix) X],
      ¬ GeometricAction (ArtinGroup explicitMatrix) X) := by
  sorry

end ArtinCAT0
end OAI
