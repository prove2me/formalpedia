-- Prove2me | Theorems.Thm_Grunbaum2003_combinatorial_types_effectively_enumerable
-- name    : Grunbaum2003.combinatorial_types_effectively_enumerable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:39:45.379801+00:00
-- url     : https://prove2.me/theorems/5572322a-bb1c-4c10-afb4-a57ade4996f5
-- title:
--   Theorem 5.5.2 — Effective enumeration of combinatorial types
-- statement:
--   There is one total computable procedure which, for every dimension d and vertex count k, returns a finite list containing exactly one incidence-scheme representative of each combinatorial type of d-polytope with k vertices.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §5.5, Theorem 5.5.2, printed p. 91 / PDF p. 117; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SchemeRealizes
import Mathlib.Computability.Partrec

set_option autoImplicit false

namespace Grunbaum2003

theorem combinatorial_types_effectively_enumerable :
    ∃ E : ℕ → ℕ → List (List (List ℕ)), Computable₂ E ∧
      ∀ d k : ℕ,
        (∀ S ∈ E d k, ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ∧
        (∀ P : Set (Fin d → ℝ), IsDPolytope P → faceCount P 0 = k →
          ∃ S ∈ E d k, SchemeRealizes k S P) ∧
        (∀ i j : Fin (E d k).length,
          ∀ P Q : Set (Fin d → ℝ),
            SchemeRealizes k ((E d k).get i) P →
            SchemeRealizes k ((E d k).get j) Q →
            Nonempty (PolytopeFace P ≃o PolytopeFace Q) → i = j) := by sorry

end Grunbaum2003
