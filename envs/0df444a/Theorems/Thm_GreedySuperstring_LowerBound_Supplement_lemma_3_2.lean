-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_Supplement_lemma_3_2
-- name    : GreedySuperstring.LowerBound.Supplement.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:38:26.052208+00:00
-- url     : https://prove2.me/theorems/ecfba724-101e-48b5-b81d-caf0edc4a736
-- title:
--   Lemma 3.2 — counting Lyndon words whose cyclic substrings occur in a word
-- statement:
--   Fix a linear order on the alphabet. Let $u$ be a word, let $m$ be an integer with $1\le m\le|u|$, and let $z_1,\dots,z_a$ be distinct Lyndon words, $a\ge0$. Suppose that $|z_j|\le m$ and $\mathrm{CSub}_m(z_j)\subseteq\mathrm{Sub}_m(u)$ for every $j$. Then
--
--   $$a\le|\mathrm{Sub}_m(u)|-|\mathrm{Sub}_{m-1}(u)|+1.$$
--
--   This counting lemma is the paper's own new ingredient: summed over $m$, it converts the substrings guaranteed by Lemma 2.4 into the bound $O\le\mathrm{OPT}+W$ of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: distinct Lyndon words z₁,…,z_a with a ≥ 0 → a finite set Z of Lyndon words with a = |Z|; reason: distinctness is the set structure; the empty set gives a = 0
--   - encoding: a ≤ |Sub_m(u)| − |Sub_{m−1}(u)| + 1 → |Z| + |Sub_{m−1}(u)| ≤ |Sub_m(u)| + 1 in ℕ; reason: the same inequality rearranged to avoid truncated subtraction
--   - encoding: finite words over an arbitrary finite alphabet → lists over an arbitrary alphabet type with decidable equality (a linear order for Lyndon words); reason: each finite instance and its run uses finitely many symbols, so restriction to the occurring symbols recovers the source setting; length counts symbols
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, Lemma 3.2, printed p.10 = PDF p.10

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_WordCombinatorics

universe l32_u

namespace GreedySuperstring.LowerBound.Supplement

/-- Lemma 3.2, printed/PDF p.10. Let `u` be a word, `1 ≤ m ≤ |u|`, and `Z` a finite set of
`a = |Z| ≥ 0` distinct Lyndon words with `|z| ≤ m` and `CSub_m(z) ⊆ Sub_m(u)` for each
`z ∈ Z`. Then `a ≤ |Sub_m(u)| − |Sub_{m−1}(u)| + 1`, written without truncated subtraction. -/
theorem lemma_3_2 {α : Type l32_u} [LinearOrder α]
    (u : List α) (m : ℕ) (hm1 : 1 ≤ m) (hmu : m ≤ u.length) (Z : Finset (List α))
    (hZ : ∀ z ∈ Z, IsLyndon z ∧ z.length ≤ m ∧ cyclicSubwords m z ⊆ subwords m u) :
    Z.card + (subwords (m - 1) u).card ≤ (subwords m u).card + 1 := by sorry

end GreedySuperstring.LowerBound.Supplement
