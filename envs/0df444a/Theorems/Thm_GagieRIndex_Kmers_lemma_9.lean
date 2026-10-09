-- Prove2me | Theorems.Thm_GagieRIndex_Kmers_lemma_9
-- name    : GagieRIndex.Kmers.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:36.952911+00:00
-- url     : https://prove2.me/theorems/55912f56-48f1-4eda-911c-8518f2b52b3f
-- title:
--   Lemma 9, p. 17 — at most 2rs distinct s-mers
-- statement:
--   Let $T[1..n]$ be a text whose BWT has $r$ runs. For every integer $s$ with $1\le s\le n$, the set $\mathcal S_s(T)$ of distinct substrings of length $s$ satisfies
--   $$|\mathcal S_s(T)|\le 2rs.$$
--
--   This is the exact combinatorial bound on substring complexity underlying the paper's space claims for its text index.
--
--   **Formalization Note** The finite set counts each string once, even if it occurs in many windows. Windows may end at the unique terminator. The suffix array is a sorted permutation of positions; the BWT and $r$ are computed from it.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 17, Lemma 9

import Mathlib
import Definitions.Def_GagieRIndex_Kmers_Smers

namespace GagieRIndex.Kmers

theorem lemma_9 (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (s : ℕ) (hs1 : 1 ≤ s) (hsn : s ≤ n) :
    (smers n T s).card ≤ 2 * GagieRIndex.Locate.runs n T SA * s := by sorry

end GagieRIndex.Kmers
