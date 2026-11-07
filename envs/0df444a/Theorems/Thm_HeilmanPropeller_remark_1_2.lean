-- Prove2me | Theorems.Thm_HeilmanPropeller_remark_1_2
-- name    : HeilmanPropeller.remark_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:35:28.350273+00:00
-- url     : https://prove2.me/theorems/87ed47e9-0235-41ed-8e0f-e033fe4c875e
-- title:
--   Remark 1.2: equality in the propeller inequality only for three $120^\circ$ sectors
-- statement:
--   Throughout, $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$ (Euclidean norm), and for a partition $\mathcal A=(A_1,\dots,A_k)$ the Gaussian moments, cell measures and value are
--
--   $$z_i=\int_{A_i}x\,d\gamma_n(x),\qquad p_i=\gamma_n(A_i),\qquad F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2 .$$
--
--   $C_k=\sup_{n\ge1}\sup_{\mathcal A}F(\mathcal A)$, the supremum over partitions of $\mathbb R^n$ into $k$ sets (display (1.1)).
--
--   Let $n,N\ge1$ and let $\mathcal A=(A_1,\dots,A_N)$ be a partition of $\mathbb R^n$ into measurable sets with
--
--   $$F(\mathcal A)=\sum_{i=1}^N\|z_i\|^2=\frac{9}{8\pi}.$$
--
--   Then $n\ge2$, $N\ge3$, and up to measure zero changes, a rotation of $\mathbb R^n$ and a relabeling of the cells,
--
--   $$\mathcal A=(B_1\times\mathbb R^{n-2},\ B_2\times\mathbb R^{n-2},\ B_3\times\mathbb R^{n-2},\ \emptyset,\dots,\emptyset),$$
--
--   where $B_1,B_2,B_3\subseteq\mathbb R^2$ are the three $120^\circ$ cones centred at the origin.
--
--   Theorem 1.1 ($\sup F=9/(8\pi)$, Khot–Naor's propeller conjecture) says the propeller is optimal; this remark says it is the only optimal partition. Through the equivalences of Theorem 1.3 it gives uniqueness in the probabilistic and analytic forms (Remark 1.4).
--
--   **Formalization Note** $B_i\times\mathbb R^{n-2}$ are the reused `propeller n N` cells (closed sectors in coordinates $0,1$; the cells $3,\dots,N-1$ are empty). A rotation is a linear isometry of determinant $1$, a relabeling a permutation of the cells, and "up to measure zero changes" is almost-everywhere equality of sets for $\gamma_n$.
--
--   Differences from the source:
--   - generalization: A is a finite measurable partition of the space → IsPartition A: measurable cells, γ-almost every point in exactly one cell; reason: every exact partition is one, and the statement specializes to exact partitions
--   - encoding: n, N ≥ 1 (display (1.1)) → all n N : ℕ; reason: at n = 0 every partition has value 0 and at N = 0 there is no partition, so no instance is added
--   - encoding: rotations; B₁, B₂, B₃ each 120 degree cones centered at the origin → a linear isometry R of determinant 1 applied to the fixed sectors propeller n N; reason: any three 120° cones partitioning a plane through the origin are a rotation of the fixed ones
--   - encoding: the printed tuple (B₁ × ℝⁿ⁻², B₂ × ℝⁿ⁻², B₃ × ℝⁿ⁻², ∅, …, ∅) → conclusion 3 ≤ N together with the a.e. equalities; reason: the tuple names three cells
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), Remark 1.2, p.1

import Mathlib
import Definitions.Def_GaussianPropeller

namespace HeilmanPropeller

open MeasureTheory OAI.GaussianPropeller

/-- **Remark 1.2 (equality only for the propeller).** Heilman, *On the Propeller Conjecture*,
arXiv:2610.32158 (held version, sha256 13f5ddf8…), Remark 1.2, p.1.

If a partition `A = (A₁, …, A_N)` of `ℝⁿ` has `F(A) = 9/(8π)`, then `n ≥ 2`, `N ≥ 3`, and up to
measure zero changes, a rotation of `ℝⁿ` and a relabeling of the cells,
`A = (B₁ × ℝⁿ⁻², B₂ × ℝⁿ⁻², B₃ × ℝⁿ⁻², ∅, …, ∅)` with `B₁, B₂, B₃` the three `120°` sectors of the
plane centred at the origin.

**Formalization Note.**
* Partitions are `IsPartition` (measurable cells, `γₙ`-a.e. point in exactly one cell), weaker
  than exact partitions; `value` is `F` and `gaussian n` is `γₙ` on `EuclideanSpace ℝ (Fin n)`.
* `propeller n N` (reused) is, for `n ≥ 2`, the three closed `120°` sectors `|θ| ≤ 60°`,
  `60° ≤ θ ≤ 180°`, `−180° ≤ θ ≤ −60°` in coordinates `0, 1`, times the remaining coordinates, and
  `∅` for cells `3, …, N − 1`. Any three `120°` cones of a plane through the origin that partition it
  are the image of these under a rotation, so "each `120°` cones centered at the origin" is carried by
  `R`.
* "Rotation" is a linear isometry of determinant `1`; "relabeling" is a permutation `σ` of the cells;
  "up to measure zero changes" is `=ᵐ[gaussian n]`. `N ≥ 3` is the printed tuple's three named
  cells. -/
theorem remark_1_2 (n N : ℕ) (A : Fin N → Set (Space n)) (hA : IsPartition A)
    (hF : value A = 9 / (8 * Real.pi)) :
    2 ≤ n ∧ 3 ≤ N ∧ ∃ (R : Space n ≃ₗᵢ[ℝ] Space n) (σ : Equiv.Perm (Fin N)),
      LinearMap.det (R.toLinearEquiv : Space n →ₗ[ℝ] Space n) = 1 ∧
      ∀ i, A (σ i) =ᵐ[gaussian n] R '' propeller n N i := by sorry

end HeilmanPropeller
