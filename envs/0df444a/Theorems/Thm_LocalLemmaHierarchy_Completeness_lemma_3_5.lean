-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_lemma_3_5
-- name    : LocalLemmaHierarchy.Completeness.lemma_3_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T00:19:54.298607+00:00
-- url     : https://prove2.me/theorems/36ce5e19-2219-47f4-b80c-de34d9c1c2ae
-- title:
--   Lemma 3.5 — geometric suffix averaging: error $(Y^{(0)}-Y^{(q)})/q\le 1/q$
-- statement:
--   Let $F$ have rows $F_s(x)=\sum_{a\in\mathcal A_s}t_{s,a}\prod_{u\in C(s,a)}(1-x_u)^{-1}$, $t_{s,a}>0$, with finitely many options and factor occurrences per row. If $q\ge1$, $0\le b<1$, and $Y^{(0)},\dots,Y^{(q)}\in[0,b]^S$ satisfy $F(Y^{(j)})\le Y^{(j-1)}$ for $1\le j\le q$, then
--   $$\bar x_s=1-\Bigl(\prod_{j=1}^q(1-Y^{(j)}_s)\Bigr)^{1/q}\qquad(3.5)$$
--   lies in $[0,b]^S$ and satisfies $F_s(\bar x)\le\bar x_s+(Y^{(0)}_s-Y^{(q)}_s)/q\le\bar x_s+1/q$ (3.6).
--
--   Differences from the source:
--   - encoding: F : [0,1)^S → [0,∞)^S → productRowUpdate A t C, defined for every x : S → ℝ and applied only to vectors in [0,b]^S; reason: the conclusion only evaluates F at Y^(j) and x̄, which lie in [0,b]^S ⊆ [0,1)^S
--   - encoding: finitely many options and factor occurrences per row → options A s : Finset ι, factor occurrences C s a : Multiset S; reason: Finset and Multiset are finite; the multiset keeps repeated factors
--   - encoding: vectors Y^(0), …, Y^(q) → Y : ℕ → S → ℝ, only Y 0, …, Y q constrained; reason: the other values never occur in the statement
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Lemma 3.5, printed p. 9 (PDF p. 11), proved there

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory

namespace LocalLemmaHierarchy.Completeness

/-- **Lemma 3.5 (Geometric suffix averaging)**, printed p. 9 / PDF 11. Let
`F_s(x) = ∑_{a ∈ A_s} t_{s,a} ∏_{u ∈ C(s,a)} (1 − x_u)⁻¹` with `t_{s,a} > 0`, finitely many options and
factor occurrences per row. If `q ≥ 1`, `0 ≤ b < 1`, and `Y^(0), …, Y^(q) ∈ [0, b]^S` satisfy
`F(Y^(j)) ≤ Y^(j−1)` for `1 ≤ j ≤ q`, then `x̄_s = 1 − (∏_{j=1}^q (1 − Y^(j)_s))^{1/q}` (3.5) lies in
`[0, b]^S` and `F_s(x̄) ≤ x̄_s + (Y^(0)_s − Y^(q)_s)/q ≤ x̄_s + 1/q` (3.6). -/
theorem lemma_3_5 {S ι : Type} (A : S → Finset ι) (t : S → ι → ℝ) (C : S → ι → Multiset S)
    (ht : ∀ s, ∀ a ∈ A s, 0 < t s a) (q : ℕ) (hq : 1 ≤ q) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (Y : ℕ → S → ℝ) (hY : ∀ j ≤ q, ∀ s, 0 ≤ Y j s ∧ Y j s ≤ b)
    (hF : ∀ j, 1 ≤ j → j ≤ q → ∀ s, productRowUpdate A t C (Y j) s ≤ Y (j - 1) s) :
    let xbar : S → ℝ := fun s => 1 - (∏ j ∈ Finset.Icc 1 q, (1 - Y j s)) ^ ((1 : ℝ) / q)
    (∀ s, 0 ≤ xbar s ∧ xbar s ≤ b) ∧
    ∀ s, productRowUpdate A t C xbar s ≤ xbar s + (Y 0 s - Y q s) / q ∧
      xbar s + (Y 0 s - Y q s) / q ≤ xbar s + 1 / q := by sorry

end LocalLemmaHierarchy.Completeness
