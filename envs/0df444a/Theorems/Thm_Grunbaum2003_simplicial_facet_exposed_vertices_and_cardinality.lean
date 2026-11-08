-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_facet_exposed_vertices_and_cardinality
-- name    : Grunbaum2003.simplicial_facet_exposed_vertices_and_cardinality
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T02:55:42.498106+00:00
-- url     : https://prove2.me/theorems/e911745e-07a7-47d9-b6eb-730cc21d22eb
-- title:
--   Exposed-vertex characterization and cardinality $d$ of every facet of a simplicial $d$-polytope
-- statement:
--   For any simplicial $d$-polytope $P \subseteq \mathbb{R}^d$ (`IsSimplicialDPolytope P`) satisfying the exposed-vertex hull representation and any facet $F$ of $P$ (`F.Nonempty`, `IsExposed ℝ P F`, and $\operatorname{finrank}_{\mathbb{R}}(\operatorname{aff}(F).\mathrm{direction}) + 1 = d$), there exists an affinely independent, injective family $v : \operatorname{Fin} d \to \mathbb{R}^d$ of exposed vertices of $P$ (`∀ i : Fin d, IsExposed ℝ P {v i}`) such that $F = \operatorname{convexHull} \mathbb{R} (\operatorname{Set.range} v)$, $F \cap \operatorname{vert}(P) = \operatorname{Set.range} v$, and $\#(F \cap \operatorname{vert}(P)) = d$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §4.5, p. 57

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent

set_option autoImplicit false

namespace Grunbaum2003

theorem simplicial_facet_exposed_vertices_and_cardinality :
  ∀ {d : ℕ} {P : Set (Fin d → ℝ)},
    IsSimplicialDPolytope P →
    ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
    ∀ (F : Set (Fin d → ℝ)), F.Nonempty → IsExposed ℝ P F →
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d →
      ∃ v : Fin d → Fin d → ℝ,
        AffineIndependent ℝ v ∧
        Function.Injective v ∧
        (∀ i : Fin d, IsExposed ℝ P {v i}) ∧
        F = convexHull ℝ (Set.range v) ∧
        F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = Set.range v ∧
        (F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}).ncard = d := by sorry

end Grunbaum2003
