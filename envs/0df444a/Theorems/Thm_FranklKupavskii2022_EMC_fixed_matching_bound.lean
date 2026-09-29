-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_fixed_matching_bound
-- name    : FranklKupavskii2022.EMC.fixed_matching_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:20:59.039289+00:00
-- url     : https://prove2.me/theorems/0d07c5dc-213e-4c99-828c-8bfb0f06e97c
-- title:
--   Lemma 18: weighted count of a fixed $t$-matching against cross-dependent nested families
-- statement:
--   Let $s\in\mathbb N$, let $x,q$ be reals with $1\le x\le s+1$ and $1\le q\le s+1$, and let $t\in\mathbb N$ with $t\ge s+x+1$. Let $\mathcal F_1,\dots,\mathcal F_{s+1}\subseteq\binom Yl$ be cross-dependent and nested, with $|Y|\ge tl$, and fix a $t$-matching $\mathcal B=(B_1,\dots,B_t)$ of $l$-element subsets of $Y$. Write $|\mathcal B\cap\mathcal F_i|$ for the number of $j$ with $B_j\in\mathcal F_i$ and $W=\sum_{i=1}^s|\mathcal B\cap\mathcal F_i|+q|\mathcal B\cap\mathcal F_{s+1}|$. Then
--
--   $$
--   W\le st+q|\mathcal B\cap\mathcal F_{s+1}|-sx\quad\text{if } |\mathcal B\cap\mathcal F_{s+1}|\ge x, \tag{30}
--   $$
--
--   $$
--   W\le st-|\mathcal B\cap\mathcal F_{s+1}|\Big(x-\frac{q|\mathcal B\cap\mathcal F_{s+1}|}{s+1}\Big)\quad\text{if } |\mathcal B\cap\mathcal F_{s+1}|\le x. \tag{31}
--   $$
--
--   This deterministic bound is averaged over a random matching in the proof of Lemma 15.
--
--   **Formalization Note** The matching is an ordered tuple of pairwise disjoint $l$-sets; the intersection sizes count positions.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Lemma 18, p. 11

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_tMatchings
import Definitions.Def_FranklKupavskii2022_EMC_CrossDependent
import Definitions.Def_FranklKupavskii2022_EMC_Nested

namespace FranklKupavskii2022.EMC

/-- Lemma 18 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 11): let `1 ≤ x, q ≤ s + 1` and
`t ≥ s + x + 1`, `t ∈ ℕ`. Let the families `F_1, …, F_{s+1} ⊂ \binom{Y}{l}` be cross-dependent and
nested, and suppose that `|Y| ≥ tl`. Fix any `t`-matching `B` of `l`-element sets in `Y`. Then
`|B ∩ F_1| + … + |B ∩ F_s| + q|B ∩ F_{s+1}| ≤ st + q|B ∩ F_{s+1}| − sx` (30) for
`|B ∩ F_{s+1}| ≥ x`, and
`|B ∩ F_1| + … + |B ∩ F_s| + q|B ∩ F_{s+1}| ≤ st − |B ∩ F_{s+1}|(x − q|B ∩ F_{s+1}|/(s+1))` (31)
for `|B ∩ F_{s+1}| ≤ x`.

**Formalization Note.** `x, q` are real; "1 ≤ x, q ≤ s + 1" is read as `1 ≤ x ≤ s + 1` and
`1 ≤ q ≤ s + 1`. The families are `Fam 1, …, Fam (s + 1)`. The matching is an ordered tuple
`B : Fin t → Finset ℕ` of pairwise disjoint `l`-subsets of `Y`, and `|B ∩ F_i|` is `eta (Fam i) B`,
the number of positions `j` with `B_j ∈ F_i` (for `l ≥ 1` the `B_j` are distinct, so this is the
size of the set intersection). -/
theorem fixed_matching_bound (s t l : ℕ) (x q : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ s + 1) (hq1 : 1 ≤ q)
    (hq2 : q ≤ s + 1) (ht : (s : ℝ) + x + 1 ≤ t) (Y : Finset ℕ) (Fam : ℕ → Finset (Finset ℕ))
    (hFam : ∀ i ∈ Finset.Icc 1 (s + 1), Fam i ⊆ Y.powersetCard l)
    (hcross : CrossDependent s Fam) (hnest : Nested s Fam) (hY : t * l ≤ Y.card)
    (B : Fin t → Finset ℕ) (hB : ∀ j, B j ∈ Y.powersetCard l)
    (hBdisj : ∀ i j : Fin t, i ≠ j → Disjoint (B i) (B j)) :
    (x ≤ (eta (Fam (s + 1)) B : ℝ) →
        ∑ i ∈ Finset.Icc 1 s, (eta (Fam i) B : ℝ) + q * eta (Fam (s + 1)) B ≤
          s * t + q * eta (Fam (s + 1)) B - s * x) ∧
      ((eta (Fam (s + 1)) B : ℝ) ≤ x →
        ∑ i ∈ Finset.Icc 1 s, (eta (Fam i) B : ℝ) + q * eta (Fam (s + 1)) B ≤
          s * t - eta (Fam (s + 1)) B * (x - q * eta (Fam (s + 1)) B / (s + 1))) := by sorry

end FranklKupavskii2022.EMC
