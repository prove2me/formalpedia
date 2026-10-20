-- Prove2me | Theorems.Thm_Gerver_injectivity
-- name    : Gerver.injectivity
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T20:13:48.694336+00:00
-- url     : https://prove2.me/theorems/5f3bf9be-473b-4e10-a6cd-852fc7aa5e56
-- title:
--   The rotation path of a maximum-area sofa satisfies the injectivity condition
-- statement:
--   The rotation path of a balanced maximum sofa of rotation angle π/2 that attains the maximum sofa area satisfies the injectivity condition: it is continuously differentiable, and on the open interval (0, π/2) its derivative points strictly against the inner wall direction u_t and strictly along the outer wall direction v_t. Geometrically, the contact path of a maximizer never loops back on itself — it sweeps monotonically through the turn. The formal statement abridges the source's injectivity condition by dropping its auxiliary clause on the boundary curve σ_K, keeping the continuous differentiability and the two strict derivative inequalities, which are what the endgame's dominating argument consumes.
-- source:
--   Baek (2024), Optimality of Gerver's Sofa, arXiv:2411.19826, Theorem 1.7.1 and Theorem 6.1.1 (Step 2 of the proof outline)

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone
import Definitions.Def_Gerver_sofa

namespace Gerver

/-- Step 2 (Theorem 1.7.1 / Theorem 6.1.1): the rotation path of a balanced
maximum sofa of rotation angle π/2 attaining the maximum area satisfies the
injectivity condition — it is continuously differentiable, and its derivative
points strictly against u_t and along v_t on (0, π/2), so the rotation path
makes no self-loop. -/
theorem injectivity (S : Set (ℝ × ℝ)) (X : ℝ → ℝ × ℝ)
    (hbal : IsBalancedMaximumSofa S (Real.pi / 2)) (hmax : area S = sofaMax)
    (hsup : IsSupportingPathOf X (Real.pi / 2)) (hmono : S = sofaOfPath X (Real.pi / 2)) :
    SatisfiesInjectivity X := by
  sorry

end Gerver
