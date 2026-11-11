-- Prove2me | Theorems.Thm_LZEndAccess_Main_lemma_5_7
-- name    : LZEndAccess.Main.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:34:42.453793+00:00
-- url     : https://prove2.me/theorems/2a68733b-9e7f-401f-9b00-4eda9afd6c8f
-- title:
--   Lemma 5.7 — an $sJ$ step that keeps $r\ge k$ starts in the bad suffix
-- statement:
--   Let $P=S[a..b]$ be a phrase of an LZ-End factorization of $S[1..n]$, let $i\in L(P)$ with $r_i\in[k..1.5k)$ for some $k\in\mathbb K$, and let $i'=sJ(i)$. If $r_{i'}\ge k$, then
--   $$i\ \text{is in the bad suffix of } L(P).$$
--
--   The lemma reduces the stable part to walks up the single tree $T_{\mathrm{bad}}$.
--
--   Differences from the source:
--   - encoding: a string S[1..n] over an alphabet Σ → S : List ℕ with 1-based access S[i] = charAt S i; reason: the word RAM stores characters as words; no instance changes
--   - encoding: phrases P_t = S[a_t..b_t], t ∈ [1..z], each reference phrase given with the index j of its source → Z : List Phrase, phrase t = ⟨a_t, b_t, src_t⟩ (1-based), src_t = 0 for a phrase without source; reason: 0 is not a phrase index; the same factorizations, including reference phrases of length one
--   - encoding: K = {1.5^i | i ∈ [0..log_{1.5}(n/z)]} → Klev n z = {(3/2)^e | e ∈ ℕ, (3/2)^e ≤ n/z} ⊆ ℝ; reason: i ≤ log_{1.5}(n/z) iff 1.5^i ≤ n/z; the elements stay real numbers and [k..1.5k) is the set of integers in [k, 1.5k)
-- source:
--   Boneh, Gawrychowski, Random Access to LZ-End: Faster and Deterministic, arXiv:2607.14923 (sha256 3c96c6ff…), p. 25, Lemma 5.7

import Mathlib
import Definitions.Def_LZEndAccess_Main_LZEnd
import Definitions.Def_LZEndAccess_Main_StablePart

set_option autoImplicit false

namespace LZEndAccess.Main

/-- **Lemma 5.7** (p. 25). Let `P = S[a..b]` be a phrase, `i ∈ L(P)` with `r_i ∈ [k..1.5k)` for
some `k ∈ K`, and `i' = sJ(i)`. If `r_{i'} ≥ k`, then `i` is in the bad suffix of `L(P)`. -/
theorem lemma_5_7 (S : List ℕ) (Z : List Phrase) (hZ : IsLZEnd S Z)
    (t i : ℕ) (hiL : InL Z t i)
    (k : ℝ) (hk : k ∈ Klev S.length Z.length)
    (hr1 : k ≤ (rVal Z i : ℝ)) (hr2 : (rVal Z i : ℝ) < 3 / 2 * k)
    (i' : ℕ) (hi' : sJ Z i = some i') (hge : k ≤ (rVal Z i' : ℝ)) :
    InBadSuffix Z t i := by sorry

end LZEndAccess.Main
