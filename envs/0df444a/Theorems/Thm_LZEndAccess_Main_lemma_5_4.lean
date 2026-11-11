-- Prove2me | Theorems.Thm_LZEndAccess_Main_lemma_5_4
-- name    : LZEndAccess.Main.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:34:36.691624+00:00
-- url     : https://prove2.me/theorems/67c8f05c-b8e3-449a-bbcf-a57a92b4a71a
-- title:
--   Lemma 5.4 (Stable Part Properties) — $sJ$ either drops $r$ below $k$ or does not increase $\ell$
-- statement:
--   Let $\mathcal Z$ be an LZ-End factorization of $S[1..n]$, $k\in\mathbb K$, and let $i\in[1..n]$ satisfy $r_i\in[k..1.5k)$ and $\ell_i<1.5k$. Then $j=sJ(i)$ is defined and
--   $$r_j<k\quad\text{or}\quad \ell_j\le\ell_i .$$
--
--   Together with the r-monotonicity of $sJ$ this keeps the stable part of an epoch inside the regime where $sJ$ stays defined.
--
--   Differences from the source:
--   - encoding: a string S[1..n] over an alphabet Σ → S : List ℕ with 1-based access S[i] = charAt S i; reason: the word RAM stores characters as words; no instance changes
--   - encoding: phrases P_t = S[a_t..b_t], t ∈ [1..z], each reference phrase given with the index j of its source → Z : List Phrase, phrase t = ⟨a_t, b_t, src_t⟩ (1-based), src_t = 0 for a phrase without source; reason: 0 is not a phrase index; the same factorizations, including reference phrases of length one
--   - encoding: K = {1.5^i | i ∈ [0..log_{1.5}(n/z)]} → Klev n z = {(3/2)^e | e ∈ ℕ, (3/2)^e ≤ n/z} ⊆ ℝ; reason: i ≤ log_{1.5}(n/z) iff 1.5^i ≤ n/z; the elements stay real numbers and [k..1.5k) is the set of integers in [k, 1.5k)
--   - reading: Let j = sJ(i) → sJ(i) is defined (∃ j, sJ i = some j) and j satisfies the conclusion; reason: the statement names sJ(i), which presupposes it is defined; the proof's first step shows it
--   - reading: k (in §5, the level of the stable part) → k ∈ K; reason: §5 (p. 24) fixes k ∈ K; for k ≤ 0 the hypothesis r_i ∈ [k, 1.5k) is empty
-- source:
--   Boneh, Gawrychowski, Random Access to LZ-End: Faster and Deterministic, arXiv:2607.14923 (sha256 3c96c6ff…), p. 24, Lemma 5.4

import Mathlib
import Definitions.Def_LZEndAccess_Main_LZEnd
import Definitions.Def_LZEndAccess_Main_StablePart

set_option autoImplicit false

namespace LZEndAccess.Main

/-- **Lemma 5.4 (Stable Part Properties)** (p. 24). Let `i` be an index with `r_i ∈ [k..1.5k)`
(`k ∈ K`, §5) and `ℓ_i < 1.5k`, and `j = sJ(i)`. Then `sJ(i)` is defined, and either `r_j < k`
or `ℓ_j ≤ ℓ_i`. -/
theorem lemma_5_4 (S : List ℕ) (Z : List Phrase) (hZ : IsLZEnd S Z)
    (k : ℝ) (hk : k ∈ Klev S.length Z.length) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ S.length)
    (hr1 : k ≤ (rVal Z i : ℝ)) (hr2 : (rVal Z i : ℝ) < 3 / 2 * k)
    (hl : (lVal Z i : ℝ) < 3 / 2 * k) :
    ∃ j, sJ Z i = some j ∧ ((rVal Z j : ℝ) < k ∨ lVal Z j ≤ lVal Z i) := by sorry

end LZEndAccess.Main
