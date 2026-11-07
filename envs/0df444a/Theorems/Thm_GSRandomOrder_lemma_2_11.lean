-- Prove2me | Theorems.Thm_GSRandomOrder_lemma_2_11
-- name    : GSRandomOrder.lemma_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:41.249208+00:00
-- url     : https://prove2.me/theorems/46293ee7-e6fb-4abd-b9cb-5efecac3c823
-- title:
--   Lemma 2.11 — additive lower support
-- statement:
--   Let $v$ be a GS valuation and let $X\in\operatorname{dom}v$ satisfy $v(X)\ge v(Y)$ for every $Y\subseteq X$. Then there are numbers $a_g\ge0$, $g\in X$, with
--   $$
--   \sum_{g\in X}a_g=v(X)\qquad\text{and}\qquad v(Y)\ge\sum_{g\in Y}a_g\ \text{ for every }Y\subseteq X.
--   $$
--
--   The optimum of a GS valuation has an additive lower bound, which turns per-item selection probabilities into a value guarantee.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
--   - encoding: numbers a_g, g ∈ X → a function a : Fin n → ℝ, read only on X; reason: values off X are unused
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Lemma 2.11, p.8

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation

set_option autoImplicit false

namespace GSRandomOrder

/-- **Lemma 2.11 (Additive lower support)** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in
Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §2.3, p.8). Let `v` be a GS
valuation and let `X ∈ dom v` satisfy `v(X) ≥ v(Y)` for every `Y ⊆ X`. There are numbers
`a_g ≥ 0`, `g ∈ X`, with `Σ_{g ∈ X} a_g = v(X)` and `v(Y) ≥ Σ_{g ∈ Y} a_g` for every `Y ⊆ X`.

**Formalization Note.** The numbers are a function `a : Fin n → ℝ`, of which only the values on
`X` are used; sums are compared with `v` through the coercion `ℝ → WithBot ℝ`. -/
theorem lemma_2_11 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v)
    (X : Finset (Fin n)) (hX : v X ≠ ⊥) (hmax : ∀ Y ⊆ X, v Y ≤ v X) :
    ∃ a : Fin n → ℝ, (∀ g ∈ X, 0 ≤ a g) ∧ (((∑ g ∈ X, a g : ℝ)) : WithBot ℝ) = v X ∧
      ∀ Y ⊆ X, (((∑ g ∈ Y, a g : ℝ)) : WithBot ℝ) ≤ v Y := by sorry

end GSRandomOrder
