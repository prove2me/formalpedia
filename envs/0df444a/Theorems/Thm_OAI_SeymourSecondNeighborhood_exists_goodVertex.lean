-- Prove2me | Theorems.Thm_OAI_SeymourSecondNeighborhood_exists_goodVertex
-- name    : OAI.SeymourSecondNeighborhood.exists_goodVertex
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:19.812514+00:00
-- url     : https://prove2.me/theorems/ff6c5937-1ed1-4aca-80a3-92bc82508eff
-- statement:
--   The theorem states that for every finite nonempty type V with a relation r that is an oriented graph, meaning r is loopless (no v has r v v) and asymmetric (r u v implies not r v u), there exists a good vertex v. Here the first neighborhood of v is the set of w with r v w, and the second neighborhood of v is the set of w that differ from v, are not first neighbors of v, and are reached by a two-step path r v u and r u w for some u. A vertex v is good when its first neighborhood has cardinality at most that of its second neighborhood. This is the Seymour second neighborhood statement for finite oriented graphs, stated here as an admitted theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SeymourSecondNeighborhood.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SeymourSecondNeighborhood.lean; bytes 762..872
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Union
import Definitions.Def_SeymourSecondNeighborhood

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*}

variable [Fintype V] [DecidableEq V]

variable [Nonempty V]

theorem exists_goodVertex (r : V → V → Prop) (hr : IsOriented r) :
    ∃ v, GoodVertex r v := by
  sorry

end SeymourSecondNeighborhood
end OAI
