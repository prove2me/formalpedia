-- Prove2me | Theorems.Thm_LZEndAccess_Main_lemma_4_18
-- name    : LZEndAccess.Main.lemma_4_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:34:49.758211+00:00
-- url     : https://prove2.me/theorems/5d067461-147c-4523-a3df-62c81d10ab78
-- title:
--   Lemma 4.18 — all k-bad jumps of a phrase land in the same phrase
-- statement:
--   Let $k\in\mathbb K$, let $P$ be a phrase of an LZ-End factorization of $S[1..n]$, and let $i,i'\in P$ be two k-bad jumps, i.e. $r_i,r_{i'}\in[k..1.5k)$ and $r_{J(i)},r_{J(i')}\ge k$. Then
--   $$J(i)\ \text{and}\ J(i')\ \text{lie in the same phrase.}$$
--
--   This makes the k-bad parent of a phrase well defined, and hence the forests $T_k$ along which long runs of bad jumps travel.
--
--   Differences from the source:
--   - encoding: a string S[1..n] over an alphabet Σ → S : List ℕ with 1-based access S[i] = charAt S i; reason: the word RAM stores characters as words; no instance changes
--   - encoding: phrases P_t = S[a_t..b_t], t ∈ [1..z], each reference phrase given with the index j of its source → Z : List Phrase, phrase t = ⟨a_t, b_t, src_t⟩ (1-based), src_t = 0 for a phrase without source; reason: 0 is not a phrase index; the same factorizations, including reference phrases of length one
--   - encoding: K = {1.5^i | i ∈ [0..log_{1.5}(n/z)]} → Klev n z = {(3/2)^e | e ∈ ℕ, (3/2)^e ≤ n/z} ⊆ ℝ; reason: i ≤ log_{1.5}(n/z) iff 1.5^i ≤ n/z; the elements stay real numbers and [k..1.5k) is the set of integers in [k, 1.5k)
--   - reading: r_i, r′_i ∈ [k..1.5k) → r_i, r_{i'} ∈ [k, 1.5k) (inside IsKBadJump for i and i′); reason: r′_i denotes the r-value of i′, as the proof's 'both r_i and r_{i′}' shows
-- source:
--   Boneh, Gawrychowski, Random Access to LZ-End: Faster and Deterministic, arXiv:2607.14923 (sha256 3c96c6ff…), p. 16, Lemma 4.18

import Mathlib
import Definitions.Def_LZEndAccess_Main_LZEnd
import Definitions.Def_LZEndAccess_Main_NaiveJumping

set_option autoImplicit false

namespace LZEndAccess.Main

/-- **Lemma 4.18** (p. 16). For `k ∈ K`, if `i` and `i'` are two k-bad jumps in the same phrase
`P` with `r_i, r_{i'} ∈ [k..1.5k)`, then `J(i)` and `J(i')` lie in the same phrase. -/
theorem lemma_4_18 (S : List ℕ) (Z : List Phrase) (hZ : IsLZEnd S Z)
    (k : ℝ) (hk : k ∈ Klev S.length Z.length) (t i i' : ℕ)
    (hi : InPhrase Z t i) (hi' : InPhrase Z t i')
    (hbad : IsKBadJump Z k i) (hbad' : IsKBadJump Z k i') :
    ∃ t' j j', J Z i = some j ∧ J Z i' = some j' ∧ InPhrase Z t' j ∧ InPhrase Z t' j' := by sorry

end LZEndAccess.Main
