-- Prove2me | Theorems.Thm_MITMSynthesis_sortC_spec
-- name    : MITMSynthesis.sortC_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:09:06.033351+00:00
-- url     : https://prove2.me/theorems/7bc38b63-f4a3-4db1-8136-a0441a1c3ae4
-- title:
--   Sorting $S_i$ in $O(|S_i|\log|S_i|)$ time (corrected: lists of length $\ge 2$)
-- statement:
--   There is an absolute constant $C$ such that, for every list $xs$ and every key map into a linearly ordered type, merge sort in the cost monad
--
--   1. returns a permutation of $xs$,
--   2. that is sorted by the key, and
--   3. if $|xs| \ge 2$, uses at most
--   $$
--   C \cdot |xs| \cdot \log |xs|
--   $$
--   unit-cost steps (comparisons, elements moved and split steps).
--
--   In MITM-factor this is applied to $S_i$ with the order on unitaries; it is the sorting step of the paper's runtime analysis.
--
--   Differences from the source:
--   - generalization: sorting S_i under the lexicographic order on unitaries → sorting any list by any key into any linearly ordered type; reason: S_i with the unitary as key is one instance
--   - reading: O(·) → one absolute constant C, chosen before all other quantities; reason: the O-notation of an algorithm analysis is a constant independent of the input
--   - correction: O(|S_i| log |S_i|) for every S_i → the bound for lists of at least two elements; reason: counterexample: a one-element list costs one step, but |S| log |S| = 1 · log 1 = 0; S_i has |V_{n,G}|^i ≥ 2 elements whenever |V_{n,G}| ≥ 2 and i ≥ 1
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §3, p. 6 ("The set S_i can then be sorted with respect to this ordering in O(|S_i| log(|S_i|)) time")

import Mathlib
import Definitions.Def_MITMSynthesis_Timed
import Definitions.Def_MITMSynthesis_sortC

namespace MITMSynthesis

/-- **Sorting in `O(|S| log |S|)`.** Amy–Maslov–Mosca–Roetteler, arXiv:1206.0758v3, §3, p. 6:
"The set S_i can then be sorted with respect to this ordering in O(|S_i| log(|S_i|)) time".
There is one absolute constant `C` such that for every list `xs` of at least two elements and
every key into a linearly ordered type, the merge sort `sortC` returns a permutation of `xs`
sorted by the key, and its cost (comparisons, elements moved, split steps) is at most
`C · |xs| · log |xs|`. -/
theorem sortC_spec :
    ∃ C : ℝ, ∀ (β κ : Type) [LinearOrder κ] (key : β → κ) (xs : List β),
      (sortC key xs).val.Perm xs ∧
      (sortC key xs).val.Pairwise (fun a b => key a ≤ key b) ∧
      (2 ≤ xs.length →
        ((sortC key xs).cost : ℝ) ≤ C * xs.length * Real.log xs.length) := by sorry

end MITMSynthesis
