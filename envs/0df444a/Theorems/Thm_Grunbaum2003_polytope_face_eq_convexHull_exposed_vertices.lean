-- Prove2me | Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
-- name    : Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:14:29.3528+00:00
-- url     : https://prove2.me/theorems/b5bc3f50-fa90-4b5e-92fb-8a6a7c2ad1cd
-- title:
--   Exposed-vertex hull representation of polytope faces
-- statement:
--   This theorem establishes the finite exposed-vertex representation for all faces of a $d$-polytope in $\mathbb{R}^d$.
--
--   Let $d \ge 0$ be an ambient dimension and let $P \subseteq \mathbb{R}^d$ be a $d$-polytope (`IsDPolytope P`). Denote by $\operatorname{vert}(P) = \{x \in \mathbb{R}^d \mid \{x\} \text{ is an exposed face of } P\}$ the set of exposed vertices of $P$. Then:
--
--   1. The vertex set $\operatorname{vert}(P)$ is finite; and
--   2. Every exposed face $F \in \mathcal{F}(P)$ coincides with the convex hull of the exposed vertices of $P$ that lie in $F$:
--
--   $$
--   \operatorname{vert}(P) \text{ is finite} \quad \text{and} \quad \forall F \in \mathcal{F}(P),\; F = \operatorname{conv}\bigl(F \cap \operatorname{vert}(P)\bigr).
--   $$
--
--   This result provides the bridge between the geometric definition of exposed faces via supporting hyperplanes and the combinatorial representation of faces as subsets of the finite vertex set $\operatorname{vert}(P)$. In particular, it implies that face inclusion is determined by vertex inclusion ($F_1 \subseteq F_2 \iff F_1 \cap \operatorname{vert}(P) \subseteq F_2 \cap \operatorname{vert}(P)$) and that the face lattice $\mathcal{F}(P)$ is finite.
--
--   **Formalization Note** In Lean, `PolytopeFace P` is the subtype of subsets $F \subseteq \mathbb{R}^d$ satisfying `IsExposed ℝ P F`, ordered by set inclusion, and exposed vertices are points $x : \operatorname{Fin} d \to \mathbb{R}$ satisfying `IsExposed ℝ P {x}`.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §2.4 & §3.2, pp. 31–36, Theorem 3.2.2

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace Grunbaum2003

theorem polytope_face_eq_convexHull_exposed_vertices (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ F : PolytopeFace P,
        F.val = convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) := by sorry

end Grunbaum2003
