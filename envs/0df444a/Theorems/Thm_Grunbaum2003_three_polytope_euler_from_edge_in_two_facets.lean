-- Prove2me | Theorems.Thm_Grunbaum2003_three_polytope_euler_from_edge_in_two_facets
-- name    : Grunbaum2003.three_polytope_euler_from_edge_in_two_facets
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T00:26:44.639726+00:00
-- url     : https://prove2.me/theorems/4f960094-897c-4d7b-9f94-b41f7486e539
-- statement:
--   Let $P \subseteq \mathbb{R}^3$ be a $3$-polytope (`IsDPolytope P`) with exposed vertex finset $V$, edge finset $\mathcal{E}$, and facet finset $\mathcal{F}$ such that every edge $E \in \mathcal{E}$ is contained in exactly two facets $F \in \mathcal{F}$. Then Euler's polyhedral formula holds:
--
--   $$|V| + |\mathcal{F}| = |\mathcal{E}| + 2.$$

import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false
open Classical

namespace Grunbaum2003

theorem three_polytope_euler_from_edge_in_two_facets
    (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (V : Finset (Fin 3 → ℝ)) (ℰ ℱ : Finset (Set (Fin 3 → ℝ)))
    (hV_coe : (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}})
    (hℰ_coe : (ℰ : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1})
    (hℱ_coe : (ℱ : Set (Set (Fin 3 → ℝ))) =
      {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2})
    (hTwoFacets : ∀ E ∈ ℰ, (ℱ.filter (fun F => E ⊆ F)).card = 2) :
    V.card + ℱ.card = ℰ.card + 2 := by sorry

end Grunbaum2003
