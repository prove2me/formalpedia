-- Prove2me | Theorems.Thm_Grunbaum2003_vertex_figure_face_finrank_and_prescribed_cut
-- name    : Grunbaum2003.vertex_figure_face_finrank_and_prescribed_cut
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:29.127894+00:00
-- url     : https://prove2.me/theorems/393363e0-326f-402f-8804-2705b9871c56
-- title:
--   Prescribed vertex-figure hyperplane cut and affine dimension shift for exposed faces
-- statement:
--   This theorem establishes the existence of a strict separating hyperplane cut at any prescribed exposed vertex $v$ of a $d$-polytope $P \subseteq \mathbb{R}^d$ together with the affine span, nonemptiness, and dimension-shift formulas for the resulting vertex-figure face sections $G \cap l^{-1}(\{\alpha\})$.
--
--   Let $P \subseteq \mathbb{R}^d$ be a $d$-polytope (`IsDPolytope P`). Then:
--   1. **Prescribed vertex cut (`exists_vertex_cut_level_at_exposed_vertex`):** For every exposed vertex $v$ of $P$ (`IsExposed ℝ P {v}`), there exist a continuous linear functional $l \in (\mathbb{R}^d)^*$ and a level $\alpha < l(v)$ such that $l(x) \le l(v)$ for all $x \in P$, and every other exposed vertex $w \neq v$ satisfies $l(w) < \alpha$ and crosses the hyperplane $l^{-1}(\{\alpha\})$ at a unique interior segment point $\operatorname{lineMap}(v, w)(t)$ with $0 < t < 1$.
--   2. **Affine span generation (`affineSpan_vertex_figure_face_insert`):** For every exposed face $G \subseteq P$ containing $v$,
--      $$
--      \operatorname{aff}\bigl(\{v\} \cup (G \cap l^{-1}(\{\alpha\}))\bigr) = \operatorname{aff}(G).
--      $$
--   3. **Section nonemptiness (`vertex_figure_face_section_nonempty_iff`):** The section $G \cap l^{-1}(\{\alpha\})$ is nonempty if and only if $G \neq \{v\}$.
--   4. **Dimension shift (`vertex_figure_face_finrank_add_one`):** For every exposed face $G \supsetneq \{v\}$ containing $v$,
--      $$
--      \dim(\operatorname{aff} G) = \dim\bigl(\operatorname{aff}(G \cap l^{-1}(\{\alpha\}))\bigr) + 1.
--      $$
--
--   **Formalization Note** This theorem complements `exists_exposed_vertex_and_vertex_figure_orderIso` by allowing any chosen vertex $v$ and relating the native face rank $\operatorname{finrank}_{\mathbb{R}}(\operatorname{aff} G).\mathrm{direction}$ to the rank of its hyperplane section $G \cap l^{-1}(\{\alpha\})$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.4, pp. 48–50 & §12.3, p. 228

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

namespace Grunbaum2003

theorem vertex_figure_face_finrank_and_prescribed_cut (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    (∀ v : Fin d → ℝ, IsExposed ℝ P {v} →
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
              Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1)) := by sorry

end Grunbaum2003
