-- Prove2me | Theorems.Thm_Grunbaum2003_barany_por_binary_facet_growth
-- name    : Grunbaum2003.barany_por_binary_facet_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:37:16.277236+00:00
-- url     : https://prove2.me/theorems/65809ec1-5bb9-4c49-b19b-40c68ebe3ab9
-- title:
--   Bárány–Pór theorem — superexponential facet growth of 0/1-polytopes
-- statement:
--   There is a constant c > 1 and a dimension threshold D such that every d ≥ D admits a full dimensional 0/1-polytope with more than c^(d log d) facets.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §4.9, unnumbered Bárány–Pór theorem, printed p. 69a / PDF p. 94; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsZeroOnePolytope
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace Grunbaum2003

theorem barany_por_binary_facet_growth :
    ∃ c : ℝ, 1 < c ∧ ∃ D : ℕ, 2 ≤ D ∧
      ∀ d : ℕ, D ≤ d → ∃ P : Set (Fin d → ℝ),
        IsDPolytope P ∧ IsZeroOnePolytope P ∧
          c ^ ((d : ℝ) * Real.log (d : ℝ)) < (faceCount P (d - 1) : ℝ) := by sorry

end Grunbaum2003
