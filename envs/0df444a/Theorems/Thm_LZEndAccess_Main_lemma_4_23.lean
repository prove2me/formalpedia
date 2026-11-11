-- Prove2me | Theorems.Thm_LZEndAccess_Main_lemma_4_23
-- name    : LZEndAccess.Main.lemma_4_23
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:34:34.550254+00:00
-- url     : https://prove2.me/theorems/ceebaa3f-ca80-4040-b090-2b641dec9a39
-- title:
--   Lemma 4.23 — the $(x,k)$-bad jumps of a phrase form an interval, cut down by the shifted ancestor
-- statement:
--   Let $P=S[a..b]$ be a phrase of an LZ-End factorization of $S[1..n]$, $k\in\mathbb K$ and $x\ge 0$ an integer. The set of $(x,k)$-bad jumps of $P$ is an interval $[a'..b']$. Furthermore, if $P'=[c..d]$ is the $(x+1,k)$-bad parent $\pi_k^{(x+1)}(P)$ of $P$, then the $(x+1,k)$-bad jumps of $P$ are exactly
--   $$[a'..b']\cap[c+\delta_x(P)\,..\,d+\delta_x(P)].$$
--
--   The lemma is what makes the shortcut of the naive-jumping query possible: $x$ consecutive bad jumps from a phrase can be tested and taken in constant time.
--
--   Differences from the source:
--   - encoding: a string S[1..n] over an alphabet Σ → S : List ℕ with 1-based access S[i] = charAt S i; reason: the word RAM stores characters as words; no instance changes
--   - encoding: phrases P_t = S[a_t..b_t], t ∈ [1..z], each reference phrase given with the index j of its source → Z : List Phrase, phrase t = ⟨a_t, b_t, src_t⟩ (1-based), src_t = 0 for a phrase without source; reason: 0 is not a phrase index; the same factorizations, including reference phrases of length one
--   - encoding: K = {1.5^i | i ∈ [0..log_{1.5}(n/z)]} → Klev n z = {(3/2)^e | e ∈ ℕ, (3/2)^e ≤ n/z} ⊆ ℝ; reason: i ≤ log_{1.5}(n/z) iff 1.5^i ≤ n/z; the elements stay real numbers and [k..1.5k) is the set of integers in [k, 1.5k)
--   - reading: is an interval [a′..b′] → equals {i | a′ ≤ i ≤ b′} for some naturals a′, b′ (possibly empty); reason: [i..j] = ∅ for j < i (p. 4); the second part holds for every such representation
-- source:
--   Boneh, Gawrychowski, Random Access to LZ-End: Faster and Deterministic, arXiv:2607.14923 (sha256 3c96c6ff…), p. 18, Lemma 4.23

import Mathlib
import Definitions.Def_LZEndAccess_Main_LZEnd
import Definitions.Def_LZEndAccess_Main_NaiveJumping

set_option autoImplicit false

namespace LZEndAccess.Main

/-- **Lemma 4.23** (p. 18). For a phrase `P = S[a..b]`, `k ∈ K` and `x ≥ 0`, the set of
`(x, k)`-bad jumps of `P` is an interval `[a'..b']`; and if `P' = [c..d]` is the
`(x + 1, k)`-bad parent of `P`, the `(x + 1, k)`-bad jumps of `P` are exactly
`[a'..b'] ∩ [c + δ_x(P)..d + δ_x(P)]`. -/
theorem lemma_4_23 (S : List ℕ) (Z : List Phrase) (hZ : IsLZEnd S Z)
    (t : ℕ) (ht1 : 1 ≤ t) (htz : t ≤ Z.length)
    (k : ℝ) (hk : k ∈ Klev S.length Z.length) (x : ℕ) :
    (∃ a' b' : ℕ, {i | IsXKBadJump Z k x t i} = {i | a' ≤ i ∧ i ≤ b'}) ∧
    (∀ a' b' : ℕ, {i | IsXKBadJump Z k x t i} = {i | a' ≤ i ∧ i ≤ b'} →
      ∀ Q : ℕ, kAnc Z k t (x + 1) = some Q →
        {i | IsXKBadJump Z k (x + 1) t i} =
          {i | a' ≤ i ∧ i ≤ b' ∧ (ph Z Q).a + deltaX Z k x t ≤ i ∧
                i ≤ (ph Z Q).b + deltaX Z k x t}) := by sorry

end LZEndAccess.Main
