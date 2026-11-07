-- Prove2me | Theorems.Thm_HeilmanPropeller_case_k3_equality
-- name    : HeilmanPropeller.case_k3_equality
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:35:29.039395+00:00
-- url     : https://prove2.me/theorems/3a5bfc02-29cd-44b6-98f7-14cc3032b9d4
-- title:
--   Three cells: equality $F=9/(8\pi)$ only for three $120^\circ$ sectors
-- statement:
--   Throughout, $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$ (Euclidean norm), and for a partition $\mathcal A=(A_1,\dots,A_k)$ the Gaussian moments, cell measures and value are
--
--   $$z_i=\int_{A_i}x\,d\gamma_n(x),\qquad p_i=\gamma_n(A_i),\qquad F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2 .$$
--
--   $C_k=\sup_{n\ge1}\sup_{\mathcal A}F(\mathcal A)$, the supremum over partitions of $\mathbb R^n$ into $k$ sets (display (1.1)).
--
--   Let $\mathcal A=(A_1,A_2,A_3)$ be a partition of $\mathbb R^2$ into three measurable sets with
--
--   $$\|z_1\|^2+\|z_2\|^2+\|z_3\|^2=\frac{9}{8\pi}.$$
--
--   Then, up to null sets, a rotation of $\mathbb R^2$ and a relabeling of the cells, $A_1,A_2,A_3$ are the three disjoint $120^\circ$ sectors centred at the origin.
--
--   This is the equality clause of the case $k=3$ of the proof of Theorem 1.1 and Remark 1.2 (citing Khot–Naor, Corollary 3.4, Lagrange multipliers), the planar core of Remark 1.2.
--
--   **Formalization Note** The sectors are the reused `propeller 2 3`: $|\theta|\le60^\circ$, $60^\circ\le\theta\le180^\circ$, $-180^\circ\le\theta\le-60^\circ$. A rotation is a linear isometry of determinant $1$.
--
--   Differences from the source:
--   - generalization: A is a finite measurable partition of the space → IsPartition A: measurable cells, γ-almost every point in exactly one cell; reason: every exact partition is one, and the statement specializes to exact partitions
--   - generalization: the maximizing partition with three positive cells, in ℝ² after Lemma 2.1 → every three-cell IsPartition of Space 2 with value 9/(8π); reason: a maximizer with value 9/(8π) is one; a null cell would leave two cells, of value ≤ 1/π
--   - encoding: three disjoint 120 degree sectors centered at the origin, up to symmetries → A (σ i) =ᵐ R '' propeller 2 3 i with R a linear isometry of determinant 1 and σ a permutation; reason: every such triple of sectors is a rotation of the fixed one; boundary rays are null
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), proof of Theorem 1.1 and Remark 1.2, case k = 3, p.7

import Mathlib
import Definitions.Def_GaussianPropeller

namespace HeilmanPropeller

open MeasureTheory OAI.GaussianPropeller

/-- **Three cells: equality only for three `120°` sectors.** Heilman, *On the Propeller
Conjecture*, arXiv:2610.32158 (held version, sha256 13f5ddf8…), proof of Theorem 1.1 and Remark 1.2,
case `k = 3`, p.7 (citing [KN08, Corollary 3.4]).

In the plane (`n = k − 1 = 2`), a partition `A = (A₁, A₂, A₃)` of `ℝ²` with
`‖z₁‖² + ‖z₂‖² + ‖z₃‖² = 9/(8π)` is, up to null sets, a rotation and a relabeling, the three
`120°` sectors centred at the origin.

**Formalization Note.** Stated for every three-cell `IsPartition` of `ℝ²` with value `9/(8π)`, with
no positivity of the cells assumed (a null cell would leave a two-cell partition, of value
`≤ 1/π < 9/(8π)`). `propeller 2 3` (reused) is the three closed sectors `|θ| ≤ 60°`,
`60° ≤ θ ≤ 180°`, `−180° ≤ θ ≤ −60°`; the rotation is a linear isometry of determinant `1`. -/
theorem case_k3_equality (A : Fin 3 → Set (Space 2)) (hA : IsPartition A)
    (hF : value A = 9 / (8 * Real.pi)) :
    ∃ (R : Space 2 ≃ₗᵢ[ℝ] Space 2) (σ : Equiv.Perm (Fin 3)),
      LinearMap.det (R.toLinearEquiv : Space 2 →ₗ[ℝ] Space 2) = 1 ∧
      ∀ i, A (σ i) =ᵐ[gaussian 2] R '' propeller 2 3 i := by sorry

end HeilmanPropeller
