-- Prove2me | Theorems.Thm_OAI_ParityWL_parity_reduction
-- name    : OAI.ParityWL.parity_reduction
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:00.591177+00:00
-- url     : https://prove2.me/theorems/c4cc264c-7937-4f2e-bfc2-32ce8f2f23a1
-- statement:
--   The theorem states that a defined proposition, ParityReductionStatement, holds; its proof is admitted in the source. Fix k ≥ 4 and a convention c, either joint or separate, and let t = k+1 for joint and t = k for separate. Let C be a choice system on t: for each i<t a finite domain D_i, for each pair p=(i,j) with i<j a finite label set L_p, and maps from D_i and from D_j into L_p. C is successful if one can pick d_i in D_i for every i so that, for every pair i<j, the left map applied to d_i equals the right map applied to d_j; it has size at most A if every domain and label set has at most A elements. The template graph on t main vertices plus helper vertices, one for each pair i<j together with a third index m different from both, joins any two distinct main vertices and joins each helper to the main vertices i, j and m. The base graph has vertices the pairs (i, d) with d in D_i and helper vertices (h, label), and projects to the template. Its edges join (i,d) to (j,e) when the labels agree, and join a helper's label vertex to the corresponding vertices of its three indices, via the left map, the right map, or any element of the third domain. For a parity function b on template vertices, the lift has vertices (u, z), where z assigns a bit in Z/2 to each template edge at the image of u, with total b of that image; two lifted vertices are adjacent when the base vertices are adjacent and their bits agree on the shared template edge. The zero lift uses b ≡ 0 and the star lift uses b = 1 exactly at the main vertex of index 0. The conclusion is that: the two lifts have equally many vertices; for every A ≥ 1 with C of size at most A, this number is at most A·(t·2^(t−2+3·binom(t−1,2)) + 12·binom(t,3)); the zero and star lifts are k-variable Weisfeiler–Leman equivalent under convention c, meaning color-histograms of k-tuples agree for every round r, if and only if C is not successful; the same equivalence holds for the pure version, comparing tuples lying entirely in each side of their disjoint union; and if C is successful, the histograms differ at round 2 for joint or round 1 for separate, in both the ordinary and pure senses.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ParityLifts.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ParityLifts.lean; bytes 8004..8069
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ParityLifts

namespace OAI

namespace ParityWL

open scoped BigOperators

attribute [instance] ChoiceSystem.domainFintype ChoiceSystem.labelFintype

theorem parity_reduction : ParityReductionStatement := by
  sorry

end ParityWL
end OAI
