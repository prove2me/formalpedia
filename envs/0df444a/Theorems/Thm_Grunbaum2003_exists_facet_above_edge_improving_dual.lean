-- Prove2me | Theorems.Thm_Grunbaum2003_exists_facet_above_edge_improving_dual
-- name    : Grunbaum2003.exists_facet_above_edge_improving_dual
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T23:16:24.381645+00:00
-- url     : https://prove2.me/theorems/95ada7f6-0620-4fb9-88d1-ed6c617e1329
-- title:
--   Existence of an incident facet with a strictly improving third vertex above an edge of a simplicial 3-polytope
-- statement:
--   Let $P \subseteq \mathbb{R}^3$ be a simplicial $3$-polytope with finite sets of exposed vertices $V$, exposed edges $\mathcal{E}$, and exposed facets $\mathcal{F}$. Let $E \in \mathcal{E}$ be an edge containing two distinct vertices $a_0, b_0 \in V$ ($a_0 \neq b_0$), and let $h \in (\mathbb{R}^3)^*$ be a continuous linear functional such that $h(b_0) = h(a_0)$. If there exists a vertex $w \in V$ with $h(a_0) < h(w)$, then there exists a facet $F \in \mathcal{F}$ and a vertex $c \in V$ such that $E \subseteq F$, $c \in F$, and $h(a_0) < h(c)$.
--
--   **Formalization Note** Simplicial polytopes are represented by `IsSimplicialDPolytope P`.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §3.2 and §8.1–8.2, printed pp. 36–39, 130–141 / PDF pp. 58–61, 152–163

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

theorem exists_facet_above_edge_improving_dual
    (P : Set (Fin 3 → ℝ)) (hP : IsSimplicialDPolytope P)
    (V : Finset (Fin 3 → ℝ)) (ℰ ℱ : Finset (Set (Fin 3 → ℝ)))
    (hV_coe : (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}})
    (hℰ_coe : (ℰ : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1})
    (hℱ_coe : (ℱ : Set (Set (Fin 3 → ℝ))) =
      {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2}) :
    ∀ E ∈ ℰ, ∀ a₀ ∈ V, ∀ b₀ ∈ V, a₀ ∈ E → b₀ ∈ E → a₀ ≠ b₀ →
      ∀ (h : StrongDual ℝ (Fin 3 → ℝ)), h b₀ = h a₀ →
      (∃ w ∈ V, h a₀ < h w) →
      ∃ F ∈ ℱ, E ⊆ F ∧ ∃ c ∈ V, c ∈ F ∧ h a₀ < h c := by sorry

end Grunbaum2003
