-- Prove2me | Theorems.Thm_NashStackelberg_step_7_decomposition
-- name    : NashStackelberg.step_7_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:12.879793+00:00
-- url     : https://prove2.me/theorems/2b2b70ca-4432-4707-a806-de741ccb0da7
-- title:
--   Algorithm 1, Step 7, pp.11–12 — a point of the convex hull of a union of convex sets is a lottery with one point per set
-- statement:
--   Let $K_1,\dots,K_k$ be convex subsets of a real vector space and let $x\in\mathrm{conv}(K_1\cup\dots\cup K_k)$. Then there are weights $p_1,\dots,p_k\ge0$ with $\sum_j p_j=1$ and points $\hat x_1,\dots,\hat x_k$ such that
--   $$
--   x=\sum_{j=1}^k p_j\,\hat x_j,\qquad \hat x_j\in K_j\ \text{ whenever } K_j\neq\emptyset,\qquad p_j=0\ \text{ whenever } K_j=\emptyset .
--   $$
--
--   Applied to the complementarity polyhedra whose union is $\mathcal F^i$, this is Step 7 of Algorithm 1: a point $\tilde x^i\in\mathrm{conv}(\mathcal F^i)$ is written as a convex combination of pure strategies, with at most one point from each nonempty complementarity polyhedron, and the coefficients are the probabilities of the lottery.
--
--   Differences from the source:
--   - generalization: x̃ⁱ ∈ conv(𝓕ⁱ) with 𝓕ⁱ the union of the kⁱ nonempty complementarity polyhedra, written as Σⱼ pⁱⱼ x̂ⁱⱼ with x̂ⁱⱼ ∈ 𝓕ⁱ → any finitely many convex sets in a real vector space, one point from each nonempty set; reason: polyhedra are convex; the page's decomposition is the special case
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Algorithm 1, Step 7, p.12, and the paragraph "The Enumeration Algorithm", pp.11–12

import Mathlib

namespace NashStackelberg

/-- **Step 7: a point of the convex hull of a union of convex sets is a lottery over them**
(Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*,
arXiv:1910.06452v6, Algorithm 1, Step 7, p.12: "x̃ⁱ = Σ_{j=1}^{kⁱ} pⁱⱼ x̂ⁱⱼ for x̂ⁱ₁, …, x̂ⁱ_{kⁱ} ∈ 𝓕ⁱ
with pⁱⱼ ≥ 0 and Σ pⁱⱼ = 1", and pp.11–12: "the points in the support of the convex combination
belong to 𝓕ⁱ … the convex combination's coefficients pⁱ are the probabilities").

Let `K₁, …, K_k` be convex sets in a real vector space and `x ∈ conv(K₁ ∪ ⋯ ∪ K_k)`. Then there are
weights `pⱼ ≥ 0` with `Σⱼ pⱼ = 1` and points `x̂ⱼ`, with `x̂ⱼ ∈ Kⱼ` whenever `Kⱼ` is nonempty and
`pⱼ = 0` whenever `Kⱼ` is empty, such that `x = Σⱼ pⱼ x̂ⱼ`: one point per set.

**Formalization Note.** Applied with the `Kⱼ` the (at most `2^{|𝓒ⁱ|}`) polyhedra whose union is
`𝓕ⁱ`, this bounds the support of the lottery of Step 7 by the number `kⁱ` of nonempty
complementarity polyhedra, as on p.11 ("at most kⁱ"). -/
theorem step_7_decomposition {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (K : Fin k → Set E) (hK : ∀ j, Convex ℝ (K j)) {x : E} (hx : x ∈ convexHull ℝ (⋃ j, K j)) :
    ∃ (p : Fin k → ℝ) (pts : Fin k → E), (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 ∧
      (∀ j, (K j).Nonempty → pts j ∈ K j) ∧ (∀ j, K j = ∅ → p j = 0) ∧
      x = ∑ j, p j • pts j := by sorry

end NashStackelberg
