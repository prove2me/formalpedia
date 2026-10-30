-- Prove2me | Theorems.Thm_MITMSynthesis_searchAllC_spec
-- name    : MITMSynthesis.searchAllC_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:09:29.840159+00:00
-- url     : https://prove2.me/theorems/6d1fec5d-1804-4f31-8a81-35421bafabd8
-- title:
--   Searching $S^\dagger U$ in sorted $S_i$ in $O(|A|\log|S_i|)$ time (corrected: arrays of size $\ge 2$)
-- statement:
--   There is an absolute constant $C$ such that, for every array $B$ sorted by a key into a linearly ordered type and every list $A$ of queries (each a key with a payload), searching every query of $A$ in $B$ by binary search
--
--   1. returns a hit if and only if some query key is the key of some element of $B$;
--   2. if it returns a hit $(c, b)$, then $c$ is the payload of a query whose key is the key of $b$, and $b$ is an element of $B$;
--   3. if $|B| \ge 2$, uses at most
--   $$
--   C \cdot |A| \cdot \log |B|
--   $$
--   unit-cost steps.
--
--   With $A = S_{i-1}^\dagger U$ and $A = S_i^\dagger U$ and $B$ the sorted $S_i$, this gives the paper's bounds $O(|S_{i-1}|\log|S_i|)$ and $O(|S_i|\log|S_i|)$ for the collision search.
--
--   Differences from the source:
--   - generalization: searching the elements of S_{i−1}†U and S_i†U in the sorted S_i → searching any list of queries in any array sorted by any key; reason: the two searches of the paper are instances
--   - reading: searching ... can be performed → the search reports a hit iff a query occurs, and a reported hit is a genuine match; reason: a search that is fast but wrong would not perform the searching the paper describes
--   - reading: O(·) → one absolute constant C, chosen before all other quantities; reason: the O-notation of an algorithm analysis is a constant independent of the input
--   - correction: O(|A| log |S_i|) for every S_i → the bound for arrays of at least two elements; reason: counterexample: searching one query in a one-element array costs at least one step, but |A| log 1 = 0; S_i has at least two elements whenever |V_{n,G}| ≥ 2 and i ≥ 1
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §3, p. 6 ("searching for each element of S_{i−1}†U and S_i†U in S_i can be performed in time O(|S_{i−1}| log(|S_i|)) and O(|S_i| log(|S_i|)), respectively")

import Mathlib
import Definitions.Def_MITMSynthesis_Timed
import Definitions.Def_MITMSynthesis_searchC

namespace MITMSynthesis

/-- **Searching in a sorted array in `O(|A| log |B|)`.** Amy–Maslov–Mosca–Roetteler,
arXiv:1206.0758v3, §3, p. 6: "searching for each element of S_{i−1}† U and S_i† U in S_i can be
performed in time O(|S_{i−1}| log(|S_i|)) and O(|S_i| log(|S_i|)), respectively."
There is one absolute constant `C` such that, for every array `arr` sorted by a key and every
list `qs` of queries (key, payload): a hit is returned iff some query key occurs in `arr`; a
returned hit `(c, b)` pairs the payload `c` of a query with an array element `b` whose key is
that query's key; and if `arr` has at least two elements, searching all queries costs at most
`C · |qs| · log |arr|`. -/
theorem searchAllC_spec :
    ∃ C : ℝ, ∀ (β κ γ : Type) [LinearOrder κ] (key : β → κ) (arr : Array β)
      (qs : List (κ × γ)), arr.toList.Pairwise (fun a b => key a ≤ key b) →
      ((searchAllC key arr qs).val.isSome ↔ ∃ p ∈ qs, ∃ b ∈ arr.toList, key b = p.1) ∧
      (∀ c b, (searchAllC key arr qs).val = some (c, b) →
        (key b, c) ∈ qs ∧ b ∈ arr.toList) ∧
      (2 ≤ arr.size →
        ((searchAllC key arr qs).cost : ℝ) ≤ C * qs.length * Real.log arr.size) := by sorry

end MITMSynthesis
