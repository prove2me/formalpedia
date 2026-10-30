-- Prove2me | Theorems.Thm_KUModComp_interpolation
-- name    : KUModComp.interpolation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:01:25.538171+00:00
-- url     : https://prove2.me/theorems/758d031d-7436-4274-b94e-4e5dff05689a
-- title:
--   Interpolation over a commutative ring at points with unit differences
-- statement:
--   Let $R$ be a commutative ring and $\beta_0,\dots,\beta_{K-1} \in R$ with $\beta_i - \beta_j$ a unit for all $i \ne j$. Let $L_k = \prod_{j \ne k}(\beta_k - \beta_j)^{-1}(X - \beta_j)$ be the Lagrange basis. Then:
--
--   1. **Uniqueness.** If $p \in R[X]$ has $\deg p < K$ and $p(\beta_k) = 0$ for all $k$, then $p = 0$.
--   2. **Recovery.** Every $p \in R[X]$ with $\deg p < K$ satisfies
--   $$
--   p = \sum_{k<K} p(\beta_k)\, L_k .
--   $$
--   3. **Existence.** For all $y_0,\dots,y_{K-1} \in R$, the polynomial $\sum_k y_k L_k$ has degree $< K$ and takes the value $y_k$ at $\beta_k$.
--
--   This is the interpolation of Figure 1 under its hypothesis that the differences of the points are units; step 5 of the proof of Theorem 3.1 uses it with $K = N'$ to recover $f'(g_{0,0},\dots,g_{m-1,\ell-1})$ from its values.
--
--   Differences from the source:
--   - reading: Figure 1's interpolation row ("$f$ of degree $n$ with $f(\alpha_i)=\beta_i$", in $O(M(n)\log n)$ operations) and step 5 ("interpolate to recover") → the existence, uniqueness and Lagrange form of the interpolant; reason: the operation count is cited from [vzGG99], not proved in the paper, and is accounted for by the cost clause of the goal theorem; this item is the mathematical content the algorithm relies on.
--   - generalization: $N'$ points supplied to the algorithm → any number $K$ of points; reason: specializes to $K = N'$.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), Figure 1 (interpolation row) and caption, p. 8; proof of Theorem 3.1, step 5, p. 10

import Mathlib
import Definitions.Def_KUModComp_lagrangeBasis

open Polynomial

namespace KUModComp

/-- **Interpolation over a commutative ring at points with unit differences** (Kedlaya–Umans,
Dagstuhl 08381 (2008), Figure 1, interpolation row and caption, p. 8, used in step 5 of the proof of
Theorem 3.1, p. 10). Let `β_0, …, β_{K-1} ∈ R` with `β_i - β_j` a unit for `i ≠ j`. Then
1. (uniqueness) a polynomial of degree `< K` vanishing at every `β_k` is zero;
2. (recovery) every polynomial `p` of degree `< K` is `∑_k p(β_k) L_k`, with `L_k` the Lagrange
   basis `∏_{j ≠ k} (β_k - β_j)⁻¹ (X - β_j)`;
3. (existence) for all values `y_0, …, y_{K-1} ∈ R`, the polynomial `∑_k y_k L_k` has degree `< K`
   and takes the value `y_k` at `β_k`. -/
theorem interpolation {R : Type*} [CommRing R] {K : ℕ} (β : Fin K → R)
    (hβ : ∀ i j, i ≠ j → IsUnit (β i - β j)) :
    (∀ p : R[X], p.degree < K → (∀ k, p.eval (β k) = 0) → p = 0) ∧
    (∀ p : R[X], p.degree < K → p = ∑ k, C (p.eval (β k)) * lagrangeBasis β k) ∧
    (∀ y : Fin K → R, (∑ k, C (y k) * lagrangeBasis β k).degree < K ∧
      ∀ k, (∑ k', C (y k') * lagrangeBasis β k').eval (β k) = y k) := by sorry

end KUModComp
