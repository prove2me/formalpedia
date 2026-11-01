-- Prove2me | Theorems.Thm_Grunbaum2003_exists_polyTime_facet_incidence_reconstructor
-- name    : Grunbaum2003.exists_polyTime_facet_incidence_reconstructor
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T22:21:42.874926+00:00
-- url     : https://prove2.me/theorems/f25022d5-c711-4c15-af17-345a6118f0db
-- title:
--   Polynomial-time reconstruction of vertex-facet incidences from $(d-2)$-skeleton rows
-- statement:
--   This lemma states the algorithmic core of polynomial-time $(d-2)$-skeleton reconstruction (Grünbaum §12.4, p. 234a): given that every exposed face of a $d$-polytope $P$ is the convex hull of its exposed vertices, there exists a uniform polynomial-time Boolean algorithm that computes the encoded vertex-facet incidence rows from any valid encoding of the $(d-2)$-skeleton vertex-face incidence rows.
--
--   Specifically, there exists a total function $\mathcal{A} : \operatorname{List} \mathrm{Bool} \to \operatorname{List} \mathrm{Bool}$ computable in polynomial time (`ContainmentPolyTime algorithm`) such that for every dimension $d \ge 3$, every vertex count $n \in \mathbb{N}$, every $d$-polytope $P \subseteq \mathbb{R}^d$ satisfying the exposed-vertex hull property $F = \operatorname{conv}(F \cap \operatorname{vert}(P))$, every injective enumeration $v : \operatorname{Fin} n \xrightarrow{\sim} \operatorname{vert}(P)$, and every list `rows` of vertex subsets of faces of dimension at most $d - 2$ (`HasReconstructionFaceRows P v (Set.Iic (d - 2)) rows`), there exists a list `facets` of vertex subsets of facets (`HasReconstructionFaceRows P v {d - 1} facets`) satisfying
--
--   $$
--   \mathcal{A}\bigl(\operatorname{code}(d, n, \mathrm{rows})\bigr) = \operatorname{code}(d, n, \mathrm{facets}).
--   $$
--
--   In `polynomial_skeleton_reconstruction`, the exposed-vertex hull hypothesis is supplied unconditionally for every $d$-polytope $P$ by `polytope_face_eq_convexHull_exposed_vertices`.
--
--   **Formalization Note** In Lean, `HasReconstructionFaceRows P v D rows` means that `rows` is duplicate-free and its elements are precisely the vertex-index finsets $\{i \in \operatorname{Fin} n \mid v(i) \in F\}$ of nonempty exposed faces $F$ of $P$ whose affine dimension lies in $D$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §12.3 (Theorem 12.3.1, p. 228) & §12.4 (“Algorithmic aspects”, p. 234a)

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_containmentBitBlock
import Definitions.Def_Grunbaum2003_ContainmentPolyTime
import Definitions.Def_Grunbaum2003_reconstructionIncidenceCode
import Definitions.Def_Grunbaum2003_HasReconstructionFaceRows
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace Grunbaum2003

theorem exists_polyTime_facet_incidence_reconstructor :
    ∃ algorithm : List Bool → List Bool, ContainmentPolyTime algorithm ∧
      ∀ (d n : ℕ), 3 ≤ d →
        ∀ (P : Set (Fin d → ℝ)), IsDPolytope P →
          ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
            ∀ F : PolytopeFace P,
              F.val = convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
          ∀ (v : Fin n → Fin d → ℝ), Function.Injective v →
            Set.range v = {x | IsExposed ℝ P {x}} →
            ∀ rows : List (Finset (Fin n)),
              HasReconstructionFaceRows P v (Set.Iic (d - 2)) rows →
              ∃ facets : List (Finset (Fin n)),
                HasReconstructionFaceRows P v {d - 1} facets ∧
                algorithm (reconstructionIncidenceCode d n rows) =
                  reconstructionIncidenceCode d n facets := by sorry

end Grunbaum2003
