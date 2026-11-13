-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_lemma_F_1
-- name    : LocalLemmaHierarchy.Completeness.lemma_F_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T00:20:17.729383+00:00
-- url     : https://prove2.me/theorems/c47190f2-bf7f-480c-bdbe-7dc0c32fbab1
-- title:
--   Lemma F.1 — geometric interpolation of residuals (generalized Hölder)
-- statement:
--   Let $F$ have rows $F_s(x)=\sum_{a\in\mathcal A_s}t_{s,a}\prod_{u\in C(s,a)}(1-x_u)^{-1}$, $t_{s,a}>0$, with finite option sets and finite factor multisets. Take $Y^{(1)},\dots,Y^{(q)}\in[0,b]^S$ with $b<1$, and positive weights $w_1,\dots,w_q$ summing to one. Define $x$ by $1-x_s=\prod_{j=1}^q(1-Y^{(j)}_s)^{w_j}$ (F.1). Then $0\le x_s\le b$ and, at every nonzero row, $F_s(x)\le\prod_{j=1}^qF_s(Y^{(j)})^{w_j}$ (F.2). Zero rows satisfy $F_s(x)=0$.
--
--   Differences from the source:
--   - encoding: a nonzero row / a zero row → a row with a nonempty / empty option set A s; reason: with t_{s,a} > 0 and every factor ≥ 1 on [0,1), a row is the zero function exactly when it has no option
--   - encoding: finite option sets and factor multisets; vectors and weights indexed by 1, …, q → A s : Finset ι, C s a : Multiset S; Y : ℕ → S → ℝ and w : ℕ → ℝ constrained on Finset.Icc 1 q; reason: the other indices never occur in the statement
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Lemma F.1, printed p. 35 (PDF p. 37); proof printed pp. 35–36 (PDF pp. 37–38)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory

namespace LocalLemmaHierarchy.Completeness

/-- **Lemma F.1 (Geometric interpolation of residuals)**, printed p. 35 / PDF 37 (proof printed
35–36). Rows `F_s(x) = ∑_{a ∈ A_s} t_{s,a} ∏_{u ∈ C(s,a)} (1 − x_u)⁻¹`, `t_{s,a} > 0`, finite option sets
and factor multisets. For `Y^(1), …, Y^(q) ∈ [0, b]^S` with `b < 1` and positive weights
`w_1, …, w_q` summing to one, `x` defined by `1 − x_s = ∏_j (1 − Y^(j)_s)^{w_j}` (F.1) satisfies
`0 ≤ x_s ≤ b`, `F_s(x) ≤ ∏_j F_s(Y^(j))^{w_j}` at every nonzero row (F.2), and `F_s(x) = 0` at zero
rows. -/
theorem lemma_F_1 {S ι : Type} (A : S → Finset ι) (t : S → ι → ℝ) (C : S → ι → Multiset S)
    (ht : ∀ s, ∀ a ∈ A s, 0 < t s a) (q : ℕ) (b : ℝ) (hb : b < 1) (Y : ℕ → S → ℝ)
    (hY : ∀ j ∈ Finset.Icc 1 q, ∀ s, 0 ≤ Y j s ∧ Y j s ≤ b)
    (w : ℕ → ℝ) (hw : ∀ j ∈ Finset.Icc 1 q, 0 < w j) (hw1 : ∑ j ∈ Finset.Icc 1 q, w j = 1) :
    let x : S → ℝ := fun s => 1 - ∏ j ∈ Finset.Icc 1 q, (1 - Y j s) ^ w j
    (∀ s, 0 ≤ x s ∧ x s ≤ b) ∧
    (∀ s, (A s).Nonempty →
      productRowUpdate A t C x s ≤ ∏ j ∈ Finset.Icc 1 q, productRowUpdate A t C (Y j) s ^ w j) ∧
    (∀ s, A s = ∅ → productRowUpdate A t C x s = 0) := by sorry

end LocalLemmaHierarchy.Completeness
