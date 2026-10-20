-- Prove2me | Theorems.Thm_Gerver_q_upper_bound
-- name    : Gerver.q_upper_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T20:15:00.289876+00:00
-- url     : https://prove2.me/theorems/f317e49a-477d-4fda-a682-7ffea818a7e6
-- title:
--   Some Gerver sofa dominates every injectivity-constrained rotation path
-- statement:
--   Some Gerver sofa dominates in area every moving sofa whose supporting rotation path of angle π/2 satisfies the injectivity condition. This is the concavity argument at the heart of the proof: the area upper bound Q of the source is a concave functional on a convex domain of triples of convex bodies, it coincides with the sofa area at the Gerver sofa, and the Gerver sofa is its global maximizer — so every sofa meeting the injectivity condition is bounded above by a Gerver sofa in area.
-- source:
--   Baek (2024), Optimality of Gerver's Sofa, arXiv:2411.19826, Sections 1.8.2-1.8.3; Theorems 8.3.8, 8.5.7 and 8.4.6 (Step 3 of the proof outline)

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone
import Definitions.Def_Gerver_sofa

namespace Gerver

/-- Step 3 (Sections 1.8.2-1.8.3; Theorem 8.3.8, Theorem 8.5.7 and
Theorem 8.4.6): some Gerver sofa dominates in area every moving sofa whose
supporting rotation path of angle π/2 satisfies the injectivity condition.
This is the concavity argument: the area upper bound Q is a concave
functional on the convex domain of convex-body triples, it matches the sofa
area at the Gerver sofa, and the Gerver sofa is its global maximizer. -/
theorem q_upper_bound :
    ∃ G, IsGerverSofa G ∧ ∀ (X : ℝ → ℝ × ℝ), SatisfiesInjectivity X →
      IsSupportingPathOf X (Real.pi / 2) → IsMovingSofa (sofaOfPath X (Real.pi / 2)) →
      area (sofaOfPath X (Real.pi / 2)) ≤ area G := by
  sorry

end Gerver
