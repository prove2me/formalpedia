-- Prove2me | Theorems.Thm_Grunbaum2003_polynomial_skeleton_reconstruction
-- name    : Grunbaum2003.polynomial_skeleton_reconstruction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T07:06:34.393512+00:00
-- url     : https://prove2.me/theorems/6ed81823-1685-48aa-b34e-2ac698eaf895
-- title:
--   Polynomial-time reconstruction from the (d−2)-skeleton
-- statement:
--   One polynomial-time binary algorithm reconstructs the complete labelled vertex–facet incidence rows of every d-polytope with d≥3 from a complete labelled table of all nonempty faces of dimensions at most d−2.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §12.4, “Algorithmic aspects,” unnumbered polynomial-time reconstruction theorem, printed p. 234a / PDF p. 277; refers to Theorem 12.3.1; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_containmentBitBlock
import Definitions.Def_Grunbaum2003_ContainmentPolyTime
import Definitions.Def_Grunbaum2003_reconstructionIncidenceCode
import Definitions.Def_Grunbaum2003_HasReconstructionFaceRows
import Mathlib.Analysis.Convex.Exposed

set_option autoImplicit false

namespace Grunbaum2003

/-- Grünbaum (2003), §12.4, “Algorithmic aspects”, p.234a/PDF277,
with the d ≥ 3 domain of Theorem 12.3.1. One uniform polynomial-time
algorithm reconstructs all labelled vertex-facet incidences from the full
(d−2)-skeleton. The binary function is total; correctness is required only
on valid skeleton encodings. Output row order is unrestricted. The existing
finite-alphabet TM2 time model is reused, including one polynomial bound
independent of dimension. This is an algorithm-existence statement only. -/
theorem polynomial_skeleton_reconstruction :
    ∃ algorithm : List Bool → List Bool, ContainmentPolyTime algorithm ∧
      ∀ (d n : ℕ), 3 ≤ d →
        ∀ (P : Set (Fin d → ℝ)), IsDPolytope P →
          ∀ (v : Fin n → Fin d → ℝ), Function.Injective v →
            Set.range v = {x | IsExposed ℝ P {x}} →
            ∀ rows : List (Finset (Fin n)),
              HasReconstructionFaceRows P v (Set.Iic (d - 2)) rows →
              ∃ facets : List (Finset (Fin n)),
                HasReconstructionFaceRows P v {d - 1} facets ∧
                algorithm (reconstructionIncidenceCode d n rows) =
                  reconstructionIncidenceCode d n facets := by sorry

end Grunbaum2003
