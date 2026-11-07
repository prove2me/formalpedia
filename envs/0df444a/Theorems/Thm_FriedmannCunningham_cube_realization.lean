-- Prove2me | Theorems.Thm_FriedmannCunningham_cube_realization
-- name    : FriedmannCunningham.cube_realization
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T05:12:40.318593+00:00
-- url     : https://prove2.me/theorems/befaa311-d055-4c85-bb4f-ee1735b3d856
-- title:
--   Lemma 12 — realization as an AUSO
-- statement:
--   For every n≥3 the feasible set is bounded and the Boolean policy cube is realized by the actual vertex-edge graph of the graph-derived feasible polytope. Some rational objective induces an acyclic unique-sink orientation and retains every original strict improvement.
-- source:
--   Avis and Friedmann (2017), Lemma 12, §5.2. https://oliverfriedmann.com/downloads/papers/cunningham_exponential_lower_bound.pdf

import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Lemma 12: an actual polytope realization, with an objective that orients
every cube edge and retains the original strict improvements. -/
theorem cube_realization (n : ℕ) (hn : 3 ≤ n) :
    realizesCube n hn ∧
    ∃ c : Fin (cols n) → ℚ, isAUSO n hn c ∧
      ∀ σ τ, cubeOrientation n hn (program n).c σ τ → cubeOrientation n hn c σ τ := by sorry

end FriedmannCunningham
