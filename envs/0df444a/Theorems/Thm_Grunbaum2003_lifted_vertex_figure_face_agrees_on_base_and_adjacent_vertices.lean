-- Prove2me | Theorems.Thm_Grunbaum2003_lifted_vertex_figure_face_agrees_on_base_and_adjacent_vertices
-- name    : Grunbaum2003.lifted_vertex_figure_face_agrees_on_base_and_adjacent_vertices
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T02:55:43.113791+00:00
-- url     : https://prove2.me/theorems/5caf7e4a-2d8f-4345-a26c-1b96c82c5900
-- title:
--   Agreement of a lifted vertex-figure face on the base vertex and all edge-adjacent exposed vertices
-- statement:
--   Suppose $\varphi : \operatorname{SkeletonFace} P K \xrightarrow{\sim} \operatorname{SkeletonFace} Q L$ is an order isomorphism mapping $\{v\}$ to $\{v'\}$, $F \in \operatorname{PolytopeFace} P$ contains $v$, and $G \in \operatorname{PolytopeFace} Q$ contains $v'$ and satisfies the upper-interval equivalence
--   $$
--   \forall S : \operatorname{SkeletonFace} P K,\quad v \in S.\mathrm{val}.\mathrm{val} \implies ((\varphi S).\mathrm{val} \le G \iff S.\mathrm{val} \le F).
--   $$
--   Then $(\varphi(\{x\})).\mathrm{val} \le G \iff x \in F.\mathrm{val}$ holds both at $x = v$ and at every exposed vertex $w$ of $P$ that is adjacent to $v$ along a $1$-dimensional exposed face (edge) $E \in \operatorname{SkeletonFace} P K$ ($v \in E, w \in E$).
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

theorem lifted_vertex_figure_face_agrees_on_base_and_adjacent_vertices :
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
      (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
      (v' : Fin e → ℝ) (hv' : IsExposed ℝ Q {v'})
      (hφv : φ (vertexSkeletonFace P K v hv) = vertexSkeletonFace Q L v' hv')
      (F : PolytopeFace P) (hvF : v ∈ F.val)
      (G : PolytopeFace Q) (hv'G : v' ∈ G.val),
      (∀ (S : SkeletonFace P K), v ∈ S.val.val →
        ((φ S).val ≤ G ↔ S.val ≤ F)) →
      ((φ (vertexSkeletonFace P K v hv)).val ≤ G ↔ v ∈ F.val) ∧
      (∀ (w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (E : SkeletonFace P K),
        (E.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val.val).direction = 1) →
        v ∈ E.val.val → w ∈ E.val.val →
        ((φ (vertexSkeletonFace P K w hw)).val ≤ G ↔ w ∈ F.val)) := by sorry

end Grunbaum2003
