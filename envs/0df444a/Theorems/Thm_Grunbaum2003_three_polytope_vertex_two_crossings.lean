-- Prove2me | Theorems.Thm_Grunbaum2003_three_polytope_vertex_two_crossings
-- name    : Grunbaum2003.three_polytope_vertex_two_crossings
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T00:37:01.802878+00:00
-- url     : https://prove2.me/theorems/f11f0c68-8eb0-42b3-ab83-6d2ec6505516
-- statement:
--   Let $P \subseteq \mathbb{R}^3$ be a $3$-polytope (`IsDPolytope P`) with exposed vertex finset $V$, edge finset $\mathcal{E}$, and facet finset $\mathcal{F}$ such that every edge lies in two facets. For any linear functional $l$ injective on $V$ and any intermediate vertex $x \in V$ (incident to both a downward edge and an upward edge in $l$), exactly two facets $F \in \mathcal{F}$ contain a single downward edge incident to $x$.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false
open Classical

namespace Grunbaum2003

theorem three_polytope_vertex_two_crossings
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
    ∀ (l : StrongDual ℝ (Fin 3 → ℝ)),
      (∀ x ∈ V, ∀ y ∈ V, l x = l y → x = y) →
      ∀ x ∈ V,
        (∃ E_down ∈ ℰ, x ∈ E_down ∧ ∃ u ∈ V, u ∈ E_down ∧ l u < l x) →
        (∃ E_up ∈ ℰ, x ∈ E_up ∧ ∃ u ∈ V, u ∈ E_up ∧ l x < l u) →
        (ℱ.filter (fun F =>
          ((ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)).filter
            (fun E => E ⊆ F)).card = 1)).card = 2 := by sorry

end Grunbaum2003
