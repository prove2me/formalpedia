-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_lemma_4_9
-- name    : MeanCertificates1424.Hardness.Supplement.lemma_4_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T09:04:31.686198+00:00
-- url     : https://prove2.me/theorems/d5d830b8-8efa-42b4-804a-e2da10d23ce4
-- title:
--   Lemma 4.9 — amortized counter convolution
-- statement:
--   Start with $n\ge1$ singleton blocks and merge disjoint blocks $n-1$ times, a merge of blocks of sizes $A,C\ge1$ inspecting $(\min\{\kappa,A\}+1)(\min\{\kappa,C\}+1)$ pairs. The total number of inspected pairs is exactly $n-1$ if $\kappa=0$ and at most $8\kappa n$ if $\kappa\ge1$.
--
--   This is the subtree-size bound that makes the tree recurrence run in $O(nq(\kappa+1))$.
--
--   Differences from the source:
--   - encoding: n − 1 merges of disjoint blocks starting from n singletons → a binary merge tree with n leaves; reason: the merge histories are exactly such trees; the cost depends only on block sizes
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Lemma 4.9, printed p.16 (PDF p.18)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Lemma 4.9, printed p.16 / PDF p.18. For every history of `n − 1` merges of disjoint blocks
starting from `n ≥ 1` singletons (a merge tree with `n` leaves), where merging blocks of sizes
`A, C` inspects `(min{κ, A} + 1)(min{κ, C} + 1)` pairs, the total is `n − 1` if `κ = 0` and at
most `8 κ n` if `κ ≥ 1`. -/
theorem lemma_4_9 (κ : ℕ) (T : MergeTree) :
    (κ = 0 → T.cost κ = T.size - 1) ∧ (1 ≤ κ → T.cost κ ≤ 8 * κ * T.size) := by sorry

end MeanCertificates1424.Hardness.Supplement
