-- Prove2me | Theorems.Thm_Grunbaum2003_skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso
-- name    : Grunbaum2003.skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T02:14:55.644306+00:00
-- url     : https://prove2.me/theorems/14a25173-71b8-462e-99a3-e902b4a27fe8
-- title:
--   Order-theoretic preservation of $1$-dimensional exposed edges and vertex-figure $(d-1)$-polytope skeleton isomorphism
-- statement:
--   This theorem establishes two key geometric and order-theoretic bridges for Grünbaum's Theorem 12.3.1 (inductive extension of skeleton isomorphisms via vertex figures):
--   1. **Order-Theoretic Edge Preservation (`skeletonIso_finrank_one_iff`):** Under the exposed-vertex hull representation on $P \subseteq \mathbb{R}^d$ and $Q \subseteq \mathbb{R}^e$, a nonempty exposed face $F$ has affine direction dimension $1$ if and only if $F \cap \operatorname{vert}(P) = \{a, b\}$ for two distinct exposed vertices $a \ne b$. Consequently, any skeleton order isomorphism $\varphi : \operatorname{SkeletonFace} P k \xrightarrow{\sim} \operatorname{SkeletonFace} Q l$ preserves $1$-dimensional exposed faces (edges) without assuming dimension preservation on higher-dimensional faces.
--   2. **Coordinate Vertex-Figure $(d-1)$-Polytope and Upper-Interval Skeleton Isomorphism (`prescribed_vertex_figure_polytope_and_skeleton_iso`):** For any $d$-polytope $P \subseteq \mathbb{R}^d$ ($d \ge 1$) and any prescribed exposed vertex $v$ of $P$, the separating hyperplane $H = l^{-1}(\{\alpha\})$ at $v$ cuts $P$ in an affine image $f(Q_0) = P \cap l^{-1}(\{\alpha\})$ of a full-dimensional $(d-1)$-polytope $Q_0 \subseteq \mathbb{R}^{d-1}$ (`IsDPolytope Q₀`), and induces an order isomorphism $\Psi : \{G \in \operatorname{PolytopeFace} P \mid v \in G\} \xrightarrow{\sim} \operatorname{PolytopeFace} Q_0$ that shifts face dimensions down by $1$ on all faces strictly above $\{v\}$ and restricts to an order isomorphism $\{S \in \operatorname{SkeletonFace} P (k+1) \mid v \in S\} \xrightarrow{\sim} \operatorname{SkeletonFace} Q_0 k$ for every $k \in \mathbb{N}$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §12.3, pp. 228–231, Theorem 12.3.1

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem skeleton_iso_preserves_edges_and_vertex_figure_skeleton_iso :
  (∀ {d e k l : ℕ} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)},
    ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
    ({y : Fin e → ℝ | IsExposed ℝ Q {y}}.Finite ∧
      ∀ E : PolytopeFace Q,
        E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}})) →
    ∀ (φ : SkeletonFace P k ≃o SkeletonFace Q l) (S : SkeletonFace P k),
      ((φ S).val.val.Nonempty ∧
        Module.finrank ℝ (affineSpan ℝ (φ S).val.val).direction = 1) ↔
      (S.val.val.Nonempty ∧
        Module.finrank ℝ (affineSpan ℝ S.val.val).direction = 1)) ∧
  (∀ (d : ℕ), 0 < d → ∀ (P : Set (Fin d → ℝ)), IsDPolytope P →
    ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
    ((∀ v : Fin d → ℝ, IsExposed ℝ P {v} →
        ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
          α < l v ∧ (∀ x ∈ P, l x ≤ l v) ∧
          ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v →
            l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α) ∧
      (∀ (v : Fin d → ℝ) (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
        α < l v →
        (∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α) →
        ∀ (G : Set (Fin d → ℝ)), IsExposed ℝ P G → v ∈ G →
          affineSpan ℝ (insert v (G ∩ l ⁻¹' {α})) = affineSpan ℝ G ∧
          ((G ∩ l ⁻¹' {α}).Nonempty ↔ G ≠ {v}) ∧
          (G ≠ {v} →
            (G ∩ l ⁻¹' {α}).Nonempty ∧
              Module.finrank ℝ (affineSpan ℝ G).direction =
                Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1))) →
    ∀ (v : Fin d → ℝ), IsExposed ℝ P {v} →
      ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
        (Q₀ : Set (Fin (d - 1) → ℝ))
        (f : (Fin (d - 1) → ℝ) →ᵃ[ℝ] (Fin d → ℝ))
        (Ψ : {G : PolytopeFace P // v ∈ G.val} ≃o PolytopeFace Q₀),
        α < l v ∧
        (∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α) ∧
        IsDPolytope Q₀ ∧
        Function.Injective f ∧
        f '' Q₀ = P ∩ l ⁻¹' {α} ∧
        (∀ G : {G : PolytopeFace P // v ∈ G.val},
          f '' (Ψ G).val = G.val.val ∩ (P ∩ l ⁻¹' {α}) ∧
          ((Ψ G).val = ∅ ↔ G.val.val = {v}) ∧
          (G.val.val ≠ {v} →
            (Ψ G).val.Nonempty ∧
              Module.finrank ℝ (affineSpan ℝ G.val.val).direction =
                Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction + 1)) ∧
        (∀ k : ℕ,
          ∃ Ψ_skel : {S : SkeletonFace P (k + 1) // v ∈ S.val.val} ≃o
              SkeletonFace Q₀ k,
            ∀ S : {S : SkeletonFace P (k + 1) // v ∈ S.val.val},
              (Ψ_skel S).val = Ψ ⟨S.val.val, S.property⟩)) := by sorry

end Grunbaum2003
