-- Prove2me | Theorems.Thm_LZEndAccess_Main_lemma_4_6
-- name    : LZEndAccess.Main.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:33:57.795365+00:00
-- url     : https://prove2.me/theorems/4002b7e0-b91e-4d4c-b4cf-b44878e8d988
-- title:
--   Lemma 4.6 — the source jump $J$ is a legal jumping rule
-- statement:
--   Let $\mathcal Z$ be an LZ-End factorization of $S[1..n]$ and let $i\in[1..n]$ lie in a reference phrase $P$, so that $J(i)=i-\delta_P$ is defined. Then $j=J(i)$ is a legal jump for $i$:
--   $$1\le j\le i,\qquad S[j]=S[i],\qquad r_j\le r_i.$$
--
--   Every query of the paper moves from an index to another index holding the same character without increasing the r-value; this lemma is the base case for the jump $J$.
--
--   Differences from the source:
--   - encoding: a string S[1..n] over an alphabet Σ → S : List ℕ with 1-based access S[i] = charAt S i; reason: the word RAM stores characters as words; no instance changes
--   - encoding: phrases P_t = S[a_t..b_t], t ∈ [1..z], each reference phrase given with the index j of its source → Z : List Phrase, phrase t = ⟨a_t, b_t, src_t⟩ (1-based), src_t = 0 for a phrase without source; reason: 0 is not a phrase index; the same factorizations, including reference phrases of length one
--   - encoding: j ≤ i is a legal jump (Definition 4.4) → IsLegalJump also states 1 ≤ j; reason: indices of S are in [1..n]; the paper's 'index' carries this
-- source:
--   Boneh, Gawrychowski, Random Access to LZ-End: Faster and Deterministic, arXiv:2607.14923 (sha256 3c96c6ff…), p. 12, Lemma 4.6

import Mathlib
import Definitions.Def_LZEndAccess_Main_LZEnd

set_option autoImplicit false

namespace LZEndAccess.Main

/-- **Lemma 4.6** (p. 12). `J` is a legal jumping rule: whenever `J(i)` is defined, it is a legal
jump for `i` (`J(i) ≤ i`, `S[J(i)] = S[i]`, `r_{J(i)} ≤ r_i`). -/
theorem lemma_4_6 (S : List ℕ) (Z : List Phrase) (hZ : IsLZEnd S Z)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ S.length) (j : ℕ) (hj : J Z i = some j) :
    IsLegalJump S Z i j := by sorry

end LZEndAccess.Main
