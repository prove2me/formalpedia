-- Prove2me | Theorems.Thm_LZEndAccess_Main_claim_4_14
-- name    : LZEndAccess.Main.claim_4_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:34:41.954507+00:00
-- url     : https://prove2.me/theorems/2b45ed72-67cc-4523-95fc-2a5c6240746f
-- title:
--   Claim 4.14 — the marked jump $M$ halves $\min(r,\ell)$
-- statement:
--   Let $\mathcal Z$ be an LZ-End factorization of $S[1..n]$, $\mathcal M$ a set of marked phrases, $P=S[a..b]\in\mathcal M$ and $i\in P$. Let $[x..y]$ be the interval of the halved canonical partition of $[a..b]$ containing $i$ and $j=M(i)=i-\delta\text{-}\mathrm{pre}(x,y)$. Then
--   $$r_j\le m\quad\text{or}\quad \ell_j\le m,\qquad m=\frac{\min(r_i,\ell_i)}2 .$$
--
--   The claim makes $M$ a progress step: one application of $M$ at a marked phrase ends the naive-jumping part of an epoch (Lemma 3.1).
--
--   Differences from the source:
--   - encoding: a string S[1..n] over an alphabet Σ → S : List ℕ with 1-based access S[i] = charAt S i; reason: the word RAM stores characters as words; no instance changes
--   - encoding: phrases P_t = S[a_t..b_t], t ∈ [1..z], each reference phrase given with the index j of its source → Z : List Phrase, phrase t = ⟨a_t, b_t, src_t⟩ (1-based), src_t = 0 for a phrase without source; reason: 0 is not a phrase index; the same factorizations, including reference phrases of length one
--   - reading: [x..y] the interval of the halved canonical partition that contains i → every interval [x..y] of the halved canonical partition (Definition 4.11 as printed) with x ≤ i ≤ y; reason: the printed partition can leave an index uncovered or cover it twice (finding I4); quantifying over every containing interval is the reading that is never weaker
--   - encoding: a set M ⊆ Z of marked phrases and P ∈ M → M : Set ℕ of phrase indices, t ∈ M and i in phrase t; reason: phrases are named by their indices
-- source:
--   Boneh, Gawrychowski, Random Access to LZ-End: Faster and Deterministic, arXiv:2607.14923 (sha256 3c96c6ff…), p. 14, Claim 4.14

import Mathlib
import Definitions.Def_LZEndAccess_Main_LZEnd
import Definitions.Def_LZEndAccess_Main_NaiveJumping

set_option autoImplicit false

namespace LZEndAccess.Main

/-- **Claim 4.14** (p. 14). For an index `i` in a marked phrase `P ∈ M` and `j = M(i)`
(`j = i − δ-pre(x, y)`, `[x..y]` the interval of the halved canonical partition of `P`
containing `i`), `r_j ≤ m` or `ℓ_j ≤ m`, where `m = min(r_i, ℓ_i)/2`. -/
theorem claim_4_14 (S : List ℕ) (Z : List Phrase) (hZ : IsLZEnd S Z)
    (M : Set ℕ) (t : ℕ) (htM : t ∈ M) (i : ℕ) (hi : InPhrase Z t i)
    (x y : ℕ) (hxy : IsHalvedCanon Z t x y) (hxi : x ≤ i) (hiy : i ≤ y) :
    (rVal Z (i - deltaPre Z x y) : ℝ) ≤ min (rVal Z i : ℝ) (lVal Z i) / 2 ∨
      (lVal Z (i - deltaPre Z x y) : ℝ) ≤ min (rVal Z i : ℝ) (lVal Z i) / 2 := by sorry

end LZEndAccess.Main
