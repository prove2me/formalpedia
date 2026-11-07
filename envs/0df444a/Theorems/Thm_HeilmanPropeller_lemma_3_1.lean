-- Prove2me | Theorems.Thm_HeilmanPropeller_lemma_3_1
-- name    : HeilmanPropeller.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:35:24.639197+00:00
-- url     : https://prove2.me/theorems/d09b59b4-c9bb-4a52-aa1f-a3d6c21a5a02
-- title:
--   Lemma 3.1: nondegenerate four-cell critical partitions of $\mathbb R^3$
-- statement:
--   Throughout, $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$ (Euclidean norm), and for a partition $\mathcal A=(A_1,\dots,A_k)$ the Gaussian moments, cell measures and value are
--
--   $$z_i=\int_{A_i}x\,d\gamma_n(x),\qquad p_i=\gamma_n(A_i),\qquad F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2 .$$
--
--   $C_k=\sup_{n\ge1}\sup_{\mathcal A}F(\mathcal A)$, the supremum over partitions of $\mathbb R^n$ into $k$ sets (display (1.1)).
--
--   There are two numbers $\theta_1,\theta_2$ with the following property. Let $A_1,\dots,A_4$ be a partition of $\mathbb R^3$ satisfying the critical point condition (2.2),
--
--   $$A_i=\{x:\ \langle z_i,x\rangle=\max_j\langle z_j,x\rangle\}\quad\text{up to null sets},$$
--
--   with $\operatorname{span}(z_1,\dots,z_4)$ of dimension $3$ and $\gamma_3(A_i)>0$ for all $i$. Let $v_1,\dots,v_4\in S^2$ be the vertices of the partition, $\{v_i\}=S^2\cap\bigcap_{j\ne i}A_j$. Then:
--
--   1. each $A_i\cap S^2$ is the spherical triangle with vertices $\{v_j: j\ne i\}$;
--   2. after relabeling, the triangle with vertices $v_1,v_2,v_3$ is regular, of edge length $\theta=\arccos\langle v_1,v_2\rangle$, and the other three are congruent isosceles triangles: $\langle v_1,v_4\rangle=\langle v_2,v_4\rangle=\langle v_3,v_4\rangle$;
--   3. $\theta\in\{\theta_1,\theta_2\}$.
--
--   This removes the computer-assisted epsilon-net search from the three-dimensional case of the propeller conjecture: only two configurations remain.
--
--   **Formalization Note** The cells on the sphere are read on their closed representatives `closedCell z i`; a spherical triangle is the trace on $S^2$ of the convex cone spanned by its vertices, and edge lengths are spherical distances $\arccos\langle\cdot,\cdot\rangle$. The two values are quantified before the partition.
--
--   Differences from the source:
--   - reading: A₁, …, A₄ ⊆ ℝ³ satisfy the critical point condition (2.2) → A is an IsPartition with A i =ᵐ closedCell z i, z i = centroid (A i); reason: Section 3 classifies critical partitions (Section 1.1 (ii), "the partition A₁ ∩ S², …"); IsPartition is the a.e. form
--   - reading: {vᵢ} = S² ∩ ⋂_{j≠i} Aᵢ (proof, p.6) → sphere ∩ ⋂_{j ≠ i} closedCell z j = {v i}; reason: the printed index Aᵢ is a typo for Aⱼ: the intersection over j ≠ i of a single set Aᵢ is Aᵢ itself, not a point
--   - encoding: Aᵢ ∩ S² is a spherical triangle; regular with edge length θ; three congruent isosceles triangles → closedCell z i is the cone over {v j : j ≠ i}; equal inner products among v σ0, v σ1, v σ2 and among ⟨v σa, v σ3⟩; θ = arccos ⟨v σ0, v σ1⟩; reason: spherical edge lengths are arccos of inner products of unit vectors
--   - encoding: θ can take only two possible values → ∃ θ₁ θ₂ before ∀ A, θ = θ₁ ∨ θ = θ₂; reason: at most two values over all such partitions
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), Lemma 3.1, p.6; vertices defined in its proof, p.6

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

namespace HeilmanPropeller

open MeasureTheory OAI.GaussianPropeller
open OAI.GaussianPropeller.Reduction (closedCell)
open scoped RealInnerProductSpace

/-- **Lemma 3.1 (classification of nondegenerate four-cell critical partitions of `ℝ³`).**
Heilman, *On the Propeller Conjecture*, arXiv:2610.32158 (held version, sha256 13f5ddf8…),
Lemma 3.1, p.6; the vertices `vᵢ` are defined in its proof, p.6.

There are two numbers `θ₁, θ₂` such that the following holds. Let `A₁, …, A₄ ⊆ ℝ³` be a partition
satisfying the critical point condition (2.2), `Aᵢ = {x : ⟨zᵢ, x⟩ = maxⱼ ⟨zⱼ, x⟩}` up to null sets,
with `span(z₁, …, z₄)` of dimension `3` and `γ₃(Aᵢ) > 0` for all `i`. Let `vᵢ ∈ S²` be the vertices,
`{vᵢ} = S² ∩ ⋂_{j ≠ i} Aⱼ`. Then each cell is the cone over the spherical triangle on the three
vertices `vⱼ`, `j ≠ i`; after a relabeling `σ`, the cell with vertices `v_{σ0}, v_{σ1}, v_{σ2}` is a
regular spherical triangle of edge length `θ = arccos ⟨v_{σ0}, v_{σ1}⟩`, the other three cells are
congruent isosceles triangles (their edges to `v_{σ3}` all have the same length), and
`θ ∈ {θ₁, θ₂}`.

**Formalization Note.**
* "Partition" is `IsPartition`; (2.2) is `A i =ᵐ closedCell z i` with `z i = centroid (A i)`.
  The cells' sets on the sphere are read on the closed representatives `closedCell z i`.
* A spherical triangle on vertices `u, v, w` is the intersection of `S²` with the convex cone they
  span; its edge lengths are the spherical distances `arccos ⟨·, ·⟩`. Regular: all three equal.
  "Three congruent isosceles triangles": the three cells containing `v_{σ3}` each have two edges
  `arccos ⟨v_{σa}, v_{σ3}⟩`, and these are equal for `a = 0, 1, 2`; their third edges are the edges
  of the regular triangle.
* `θ₁, θ₂` are quantified before the partition, so "θ can take only two possible values" means at
  most two values for all such partitions. -/
theorem lemma_3_1 :
    ∃ θ₁ θ₂ : ℝ, ∀ A : Fin 4 → Set (Space 3), IsPartition A →
      let z : Fin 4 → Space 3 := fun i => centroid (A i)
      (∀ i, A i =ᵐ[gaussian 3] closedCell z i) →
      Module.finrank ℝ (Submodule.span ℝ (Set.range z)) = 3 →
      (∀ i, 0 < gaussian 3 (A i)) →
      ∃ (v : Fin 4 → Space 3) (σ : Equiv.Perm (Fin 4)),
        (∀ i, ‖v i‖ = 1) ∧
        (∀ i, Metric.sphere (0 : Space 3) 1 ∩ (⋂ j ∈ ({i}ᶜ : Set (Fin 4)), closedCell z j) =
          {v i}) ∧
        (∀ i, closedCell z i =
          {x | ∃ c : Fin 4 → ℝ, (∀ j, 0 ≤ c j) ∧ c i = 0 ∧ x = ∑ j, c j • v j}) ∧
        (⟪v (σ 0), v (σ 1)⟫ = ⟪v (σ 0), v (σ 2)⟫ ∧ ⟪v (σ 0), v (σ 1)⟫ = ⟪v (σ 1), v (σ 2)⟫) ∧
        (⟪v (σ 0), v (σ 3)⟫ = ⟪v (σ 1), v (σ 3)⟫ ∧ ⟪v (σ 0), v (σ 3)⟫ = ⟪v (σ 2), v (σ 3)⟫) ∧
        (Real.arccos ⟪v (σ 0), v (σ 1)⟫ = θ₁ ∨ Real.arccos ⟪v (σ 0), v (σ 1)⟫ = θ₂) := by sorry

end HeilmanPropeller
