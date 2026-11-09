-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_three_polytope_edge_in_two_facets
-- name    : Grunbaum2003.simplicial_three_polytope_edge_in_two_facets
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T23:05:44.829099+00:00
-- url     : https://prove2.me/theorems/5d5802b7-9f34-4248-bd5b-a8448c54ddc3
-- title:
--   Every edge of a simplicial 3-polytope is contained in exactly two facets
-- statement:
--   Let $P \subseteq \mathbb{R}^3$ be a simplicial $3$-polytope with finite sets of exposed vertices $V$, exposed edges $\mathcal{E}$, and exposed facets $\mathcal{F}$. Then every edge $E \in \mathcal{E}$ is contained in exactly two facets $F \in \mathcal{F}$:
--
--   $$\forall E \in \mathcal{E}, \quad |\{F \in \mathcal{F} : E \subseteq F\}| = 2.$$
--
--   **Formalization Note** Simplicial polytopes are represented by `IsSimplicialDPolytope P`.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §3.2, Theorem 3.2.1, printed pp. 36–39 / PDF pp. 58–61

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false
open Classical

namespace Grunbaum2003

theorem simplicial_three_polytope_edge_in_two_facets
    (P : Set (Fin 3 → ℝ)) (hP : IsSimplicialDPolytope P)
    (V : Finset (Fin 3 → ℝ)) (ℰ ℱ : Finset (Set (Fin 3 → ℝ)))
    (hV_coe : (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}})
    (hℰ_coe : (ℰ : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1})
    (hℱ_coe : (ℱ : Set (Set (Fin 3 → ℝ))) =
      {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2}) :
    ∀ E ∈ ℰ, (ℱ.filter (fun F => E ⊆ F)).card = 2 := by sorry

end Grunbaum2003
