-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_three_polytope_euler_from_edge_ridge_and_crossing_counts
-- name    : Grunbaum2003.simplicial_three_polytope_euler_from_edge_ridge_and_crossing_counts
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T22:38:57.748544+00:00
-- url     : https://prove2.me/theorems/0333ecbe-ef4a-49be-a081-ddf2c602dc13
-- title:
--   Euler and Dehn-Sommerville relations for simplicial 3-polytopes via generic linear sweep and bipartite incidence
-- statement:
--   Let $P \subseteq \mathbb{R}^3$ be a simplicial $3$-polytope with finite sets of exposed vertices $V$, exposed edges $\mathcal{E}$, and exposed facets $\mathcal{F}$. Suppose that:
--
--   1. Every edge $E \in \mathcal{E}$ is contained in exactly two facets $F \in \mathcal{F}$.
--   2. For every continuous linear functional $\ell$ injective on $V$ and every intermediate vertex $x \in V$ that is incident both to an edge $E_{\text{down}} \in \mathcal{E}$ with a lower endpoint $\ell(u) < \ell(x)$ and to an edge $E_{\text{up}} \in \mathcal{E}$ with a higher endpoint $\ell(x) < \ell(u)$, there are exactly two crossing facets $F \in \mathcal{F}$ at $x$ (that is, facets $F$ containing $x$ among whose edges exactly one belongs to $\mathcal{E}_x^-(\ell) = \{E \in \mathcal{E} : x \in E \text{ and } \forall w \in V \cap E,\, \ell(w) \le \ell(x)\}$).
--
--   Then every facet $F \in \mathcal{F}$ contains exactly $3$ edges of $P$, there exists a linear functional $\ell$ strictly injective on $V$, the local sweep identity $1 + r(x) = q(x) + [x = v_{\min}] + [x = v_{\max}]$ holds at every vertex $x \in V$, and the global Euler and Dehn-Sommerville relations hold:
--
--   $$f_0(P) + f_2(P) = f_1(P) + 2 \qquad \text{and} \qquad 3 f_2(P) = 2 f_1(P).$$
--
--   **Formalization Note** Simplicial polytopes are represented by `IsSimplicialDPolytope P` and $k$-face counts by `faceCount P k`.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §8.1–8.2 and §9.2, printed pp. 130–141 / PDF pp. 152–163; Günter M. Ziegler, Lectures on Polytopes (Springer GTM 152, 1995), §8.2, Theorem 8.11, pp. 242–245

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

theorem simplicial_three_polytope_euler_from_edge_ridge_and_crossing_counts
    (P : Set (Fin 3 → ℝ)) (hP : IsSimplicialDPolytope P)
    (hLocal :
      ∀ (V : Finset (Fin 3 → ℝ)) (ℰ ℱ : Finset (Set (Fin 3 → ℝ))),
        (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}} →
        (ℰ : Set (Set (Fin 3 → ℝ))) =
          {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
            Module.finrank ℝ (affineSpan ℝ E).direction = 1} →
        (ℱ : Set (Set (Fin 3 → ℝ))) =
          {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
            Module.finrank ℝ (affineSpan ℝ F).direction = 2} →
        (∀ E ∈ ℰ, (ℱ.filter (fun F => E ⊆ F)).card = 2) ∧
        (∀ (l : StrongDual ℝ (Fin 3 → ℝ)),
          (∀ x ∈ V, ∀ y ∈ V, l x = l y → x = y) →
          ∀ x ∈ V,
            (∃ E_down ∈ ℰ, x ∈ E_down ∧ ∃ u ∈ V, u ∈ E_down ∧ l u < l x) →
            (∃ E_up ∈ ℰ, x ∈ E_up ∧ ∃ u ∈ V, u ∈ E_up ∧ l x < l u) →
            (ℱ.filter (fun F =>
              ((ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)).filter
                (fun E => E ⊆ F)).card = 1)).card = 2)) :
    faceCount P 0 + faceCount P 2 = faceCount P 1 + 2 ∧
      3 * faceCount P 2 = 2 * faceCount P 1 := by sorry

end Grunbaum2003
