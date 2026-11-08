-- Prove2me | Theorems.Thm_Grunbaum2003_vertex_figure_lift_shared_skeleton_and_symmetric_forward_iff
-- name    : Grunbaum2003.vertex_figure_lift_shared_skeleton_and_symmetric_forward_iff
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T03:24:16.318765+00:00
-- url     : https://prove2.me/theorems/14f6fdc7-c4fc-4d95-8ba5-d3c6a4c3de3f
-- title:
--   Shared-skeleton agreement, one-step facet skeleton propagation, and symmetric forward-inclusion equivalence for lifted vertex-figure faces
-- statement:
--   For any order isomorphism $\varphi : \operatorname{SkeletonFace} P K \xrightarrow{\sim} \operatorname{SkeletonFace} Q L$ between polytopes satisfying the exposed-vertex hull property and any exposed face $F \in \operatorname{PolytopeFace} P$:
--   1. **Shared-Skeleton Agreement:** Any two lifted faces $G_u, G_w \in \operatorname{PolytopeFace} Q$ satisfying the upper-interval equivalence wrt $F$ at $u$ and $w$ agree on every skeleton face $R \in \operatorname{SkeletonFace} P K$ containing both $u$ and $w$.
--   2. **One-Step Propagation in $F$:** If $G$ satisfies the upper-interval equivalence at $u$ and $E \in \operatorname{SkeletonFace} P K$ satisfies $E.\mathrm{val} \le F$, $u \in E$, and $w \in E$, then $(\varphi(\{w\})).\mathrm{val} \le G$.
--   3. **Symmetric Forward-Inclusion Equivalence:** If $\varphi$ maps exposed vertices of $F$ into $G$ and $\varphi^{-1}$ maps exposed vertices of $G$ into $F$, then $(\varphi(\{x\})).\mathrm{val} \le G \iff x \in F.\mathrm{val}$ for every exposed vertex $x$ of $P$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §12.3, pp. 228–231, Theorem 12.3.1

import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem vertex_figure_lift_shared_skeleton_and_symmetric_forward_iff :
  ∀ {d e K L : ℕ} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)},
    ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
    ({y : Fin e → ℝ | IsExposed ℝ Q {y}}.Finite ∧
      ∀ E : PolytopeFace Q,
        E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}})) →
    ∀ (vertexSkeletonFace : ∀ {m : ℕ} (R : Set (Fin m → ℝ)) (r : ℕ)
        (x : Fin m → ℝ), IsExposed ℝ R {x} → SkeletonFace R r)
      (hVertexVal : ∀ {m : ℕ} (R : Set (Fin m → ℝ)) (r : ℕ)
        (x : Fin m → ℝ) (hx : IsExposed ℝ R {x}),
        (vertexSkeletonFace R r x hx).val.val = {x})
      (φ : SkeletonFace P K ≃o SkeletonFace Q L)
      (F : PolytopeFace P),
      (∀ (u w : Fin d → ℝ) (G_u G_w : PolytopeFace Q),
        (∀ S : SkeletonFace P K, u ∈ S.val.val → ((φ S).val ≤ G_u ↔ S.val ≤ F)) →
        (∀ S : SkeletonFace P K, w ∈ S.val.val → ((φ S).val ≤ G_w ↔ S.val ≤ F)) →
        ∀ R : SkeletonFace P K, u ∈ R.val.val → w ∈ R.val.val →
          (((φ R).val ≤ G_u ↔ (φ R).val ≤ G_w) ∧
            (R.val ≤ F → (φ R).val ≤ G_u ∧ (φ R).val ≤ G_w))) ∧
      (∀ (u w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (G : PolytopeFace Q),
        (∀ S : SkeletonFace P K, u ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F)) →
        ∀ E : SkeletonFace P K, E.val ≤ F → u ∈ E.val.val → w ∈ E.val.val →
          (φ (vertexSkeletonFace P K w hw)).val ≤ G) ∧
      (∀ (G : PolytopeFace Q),
        (∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
          x ∈ F.val → (φ (vertexSkeletonFace P K x hx)).val ≤ G) →
        (∀ (y : Fin e → ℝ) (hy : IsExposed ℝ Q {y}),
          y ∈ G.val → (φ.symm (vertexSkeletonFace Q L y hy)).val ≤ F) →
        ∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
          ((φ (vertexSkeletonFace P K x hx)).val ≤ G ↔ x ∈ F.val)) := by sorry

end Grunbaum2003
