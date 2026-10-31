-- Prove2me | Theorems.Thm_LeastMajorized_lemma_6_majorization_tfae
-- name    : LeastMajorized.lemma_6_majorization_tfae
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:48:47.181799+00:00
-- url     : https://prove2.me/theorems/970c8680-92cc-4167-bb55-df4ec8766895
-- title:
--   Lemma 6 — four equivalent characterizations of majorization
-- statement:
--   Let $x,y\in\mathbb R^n$. The following statements are equivalent:
--
--   1. $x\prec y$;
--   2. $\Phi(x)\le\Phi(y)$ for all continuous Schur-convex functions $\Phi:\mathbb R^n\to\mathbb R$;
--   3. $\sum_{i\in N}\phi(x_i)\le\sum_{i\in N}\phi(y_i)$ for all continuous convex functions $\phi:\mathbb R\to\mathbb R$;
--   4. $x(N)=y(N)$ and $\sum_{i\in N}\max(0,\alpha-x_i)\le\sum_{i\in N}\max(0,\alpha-y_i)$ for all $\alpha\in\mathbb R$.
--
--   These are the classical characterizations of majorization (Marshall–Olkin–Arnold, Propositions 1.A.2, 1.A.8, 4.B.1–4.B.4, as cited by the paper). Applied to $x+b$ and $y+b$, they give the equivalence of statements 2 and 3 of Theorem 5.
--
--   Differences from the source:
--   - encoding: x ≺ y ("x ≺↓ y and x(N) = y(N)") → RetailVariety.Fashion.Majorized x y (sorting permutations, equal totals, top-k partial sums for 1 ≤ k < n); reason: the case k = n of x ≺↓ y is implied by the equal totals, so this is the same relation
--   - encoding: ℝⁿ, continuous convex φ → Fin n → ℝ, ConvexOn ℝ Set.univ φ ∧ Continuous φ; reason: Lean convention; same instances
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, Lemma 6, p.7

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Majorization
import Definitions.Def_LeastMajorized_SchurConvex

namespace LeastMajorized

/-- **Lemma 6** (characterizations of majorization), Schoot Uiterkamp, *A characterization of
simultaneous optimization, majorization, and (bi)submodular polyhedra*, arXiv:2201.06596v2, p.7
(the paper refers to Marshall–Olkin–Arnold, Propositions 1.A.2, 1.A.8, 4.B.1–4.B.4). Given
vectors `x, y ∈ ℝⁿ`, the following statements are equivalent:
1. `x ≺ y`;
2. `Φ(x) ≤ Φ(y)` for all continuous Schur-convex functions `Φ`;
3. `Σ_{i∈N} φ(xᵢ) ≤ Σ_{i∈N} φ(yᵢ)` for all continuous convex functions `φ`;
4. `x(N) = y(N)` and `Σ_{i∈N} max(0, α − xᵢ) ≤ Σ_{i∈N} max(0, α − yᵢ)` for all `α ∈ ℝ`.

**Formalization Note** `ℝⁿ` is `Fin n → ℝ`; `x ≺ y` is the published
`RetailVariety.Fashion.Majorized` (decreasing rearrangements, equal totals, top-`k` partial
sums). `Φ : ℝⁿ → ℝ` is continuous for the product topology; `φ : ℝ → ℝ` is convex on `ℝ` and
continuous. -/
theorem lemma_6_majorization_tfae {n : ℕ} (x y : Fin n → ℝ) :
    List.TFAE
      [RetailVariety.Fashion.Majorized x y,
       ∀ Φ : (Fin n → ℝ) → ℝ, Continuous Φ → SchurConvex Φ → Φ x ≤ Φ y,
       ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → Continuous φ →
         ∑ i, φ (x i) ≤ ∑ i, φ (y i),
       ∑ i, x i = ∑ i, y i ∧
         ∀ α : ℝ, ∑ i, max 0 (α - x i) ≤ ∑ i, max 0 (α - y i)] := by sorry

end LeastMajorized
