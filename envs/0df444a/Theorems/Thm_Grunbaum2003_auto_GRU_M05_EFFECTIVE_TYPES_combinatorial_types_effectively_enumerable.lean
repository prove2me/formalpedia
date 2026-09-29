-- Prove2me | Theorems.Thm_Grunbaum2003_auto_GRU_M05_EFFECTIVE_TYPES_combinatorial_types_effectively_enumerable
-- name    : Grunbaum2003.auto_GRU_M05_EFFECTIVE_TYPES_combinatorial_types_effectively_enumerable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T19:11:55.314267+00:00
-- url     : https://prove2.me/theorems/65ef874a-5185-4a6c-80f4-e1836ee8f5d3
-- title:
--   Theorem 5.5.2 — Effective enumeration of combinatorial types
-- statement:
--   There is one total computable procedure which, for every natural dimension d and vertex count k, returns a finite list of incidence schemes. Every output has a realizing d-polytope with k vertices; every such polytope realizes an output; and combinatorially equivalent realizations at two output positions force those positions to coincide. Thus each combinatorial type occurs exactly once. Dimension zero uses the empty proper-face scheme for the single point.
-- source:
--   Grünbaum, Convex Polytopes, 2nd ed., Springer (2003), §5.5, Theorem 2 (5.5.2), printed p.91 / PDF117; scheme and representative-selection paragraphs on the same page.

import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_IsDPolytope
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_faceCount
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_PolytopeFace
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_SchemeRealizes
import Mathlib.Computability.Partrec

set_option autoImplicit false

namespace Grunbaum2003

theorem auto_GRU_M05_EFFECTIVE_TYPES_combinatorial_types_effectively_enumerable :
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
