-- Prove2me | Theorems.Thm_LZEndAccess_Main_lemma_5_14
-- name    : LZEndAccess.Main.lemma_5_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:34:43.025899+00:00
-- url     : https://prove2.me/theorems/8aa06a88-c6d4-48db-bfcc-e731c3470daa
-- title:
--   Lemma 5.14 — $(B)$-badness of $i_0$ versus the path sums $\Delta L$, $\Delta R$ in $T_{\mathrm{bad}}$
-- statement:
--   Let $\mathcal Z$ be an LZ-End factorization of $S[1..n]$ and let $i_0\in[1..n]$ be the input of the stable part: $r_{i_0}=R\in[k..1.5k)$ for $k\in\mathbb K$ and $\ell_{i_0}=L\le1.5k$. Let $P$ be the phrase containing $i_0$ and $B\ge0$ an integer.
--   1. If $i_0$ is a $(B)$-bad index, then $\Delta L(P,B)\le L$.
--   2. If $\Delta L(P,B)\le L$ and $\Delta R(P,B-1)\le R-k$, then $i_0$ is a $(B)$-bad index.
--   $$i_0\ (B)\text{-bad}\ \Rightarrow\ \Delta L(P,B)\le L,\qquad \Delta L(P,B)\le L\ \wedge\ \Delta R(P,B-1)\le R-k\ \Rightarrow\ i_0\ (B)\text{-bad}.$$
--
--   The lemma turns the search for the end of the stable part into two threshold queries on weighted paths of $T_{\mathrm{bad}}$.
--
--   Differences from the source:
--   - encoding: a string S[1..n] over an alphabet Σ → S : List ℕ with 1-based access S[i] = charAt S i; reason: the word RAM stores characters as words; no instance changes
--   - encoding: phrases P_t = S[a_t..b_t], t ∈ [1..z], each reference phrase given with the index j of its source → Z : List Phrase, phrase t = ⟨a_t, b_t, src_t⟩ (1-based), src_t = 0 for a phrase without source; reason: 0 is not a phrase index; the same factorizations, including reference phrases of length one
--   - encoding: K = {1.5^i | i ∈ [0..log_{1.5}(n/z)]} → Klev n z = {(3/2)^e | e ∈ ℕ, (3/2)^e ≤ n/z} ⊆ ℝ; reason: i ≤ log_{1.5}(n/z) iff 1.5^i ≤ n/z; the elements stay real numbers and [k..1.5k) is the set of integers in [k, 1.5k)
--   - reading: §5's fixed input i0 (r_{i0} = R ∈ [k..1.5k), k ∈ K, ℓ_{i0} = L ≤ 1.5k) → hypotheses on i₀ and k in the statement; reason: standing assumption of §5 (p. 24, p. 30) and the hypothesis of Lemma 3.2
--   - encoding: ΔL(P, B), ΔR(P, B) (defined while π_bad^{(B)}(P) exists and is not a root) → sums with 0 for δℓ, δr of a root and of a missing ancestor, for every B; reason: same values wherever the paper defines them; beyond, the hypotheses of part 2 cannot hold, as R − ΔR(depth − 1) is the r-value 0 of an index in a root
-- source:
--   Boneh, Gawrychowski, Random Access to LZ-End: Faster and Deterministic, arXiv:2607.14923 (sha256 3c96c6ff…), p. 29, Lemma 5.14

import Mathlib
import Definitions.Def_LZEndAccess_Main_LZEnd
import Definitions.Def_LZEndAccess_Main_StablePart

set_option autoImplicit false

namespace LZEndAccess.Main

/-- **Lemma 5.14** (p. 29). Let `i₀` be the input of the stable part (`r_{i₀} = R ∈ [k..1.5k)`,
`k ∈ K`, `ℓ_{i₀} = L ≤ 1.5k`), `P` the phrase containing it, and `B ≥ 0` an integer.
1. If `i₀` is `(B)`-bad, then `ΔL(P, B) ≤ L`.
2. If `ΔL(P, B) ≤ L` and `ΔR(P, B − 1) ≤ R − k`, then `i₀` is `(B)`-bad. -/
theorem lemma_5_14 (S : List ℕ) (Z : List Phrase) (hZ : IsLZEnd S Z)
    (k : ℝ) (hk : k ∈ Klev S.length Z.length) (i₀ : ℕ) (hi : 1 ≤ i₀) (hin : i₀ ≤ S.length)
    (hR1 : k ≤ (rVal Z i₀ : ℝ)) (hR2 : (rVal Z i₀ : ℝ) < 3 / 2 * k)
    (hL : (lVal Z i₀ : ℝ) ≤ 3 / 2 * k)
    (t : ℕ) (ht : InPhrase Z t i₀) (B : ℕ) :
    (IsXBad Z B t i₀ → DeltaL Z t B ≤ lVal Z i₀) ∧
    (DeltaL Z t B ≤ lVal Z i₀ → (DeltaR Z t ((B : ℤ) - 1) : ℝ) ≤ (rVal Z i₀ : ℝ) - k →
      IsXBad Z B t i₀) := by sorry

end LZEndAccess.Main
