-- Prove2me | Theorems.Thm_FriedmannCunningham_auso_lower_bound
-- name    : FriedmannCunningham.auso_lower_bound
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-02T05:12:50.681673+00:00
-- url     : https://prove2.me/theorems/879e6a3b-f0ee-4b0b-9ee2-a4f37a615ed2
-- title:
--   Theorem 8 — realizable-AUSO lower bound
-- statement:
--   For every n≥3 the bounded graph-derived polytope realizes a cube of dimension 5(n−1); a rational objective retaining original strict improvements gives an AUSO on which the specified signed-direction cyclic walk starts at the prescribed policy, terminates at the unique sink, and takes at least 2^n steps.
-- source:
--   Avis and Friedmann (2017), Theorem 8, §5.2. https://oliverfriedmann.com/downloads/papers/cunningham_exponential_lower_bound.pdf Uses the explicit Sections 2.3/4.4 counter start and the full counter-run transfer, resolving the shorthand Section 5.2 start.

import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Theorem 8: a realizable AUSO of dimension 5(n−1), with both signed
directions ordered as in (1), and a complete walk of length at least 2^n. -/
theorem auso_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    realizesCube n hn ∧
    ∃ (c : Fin (cols n) → ℚ) (T : ℕ) (s : ℕ → MDPState n),
      isAUSO n hn c ∧
      (∀ σ τ, cubeOrientation n hn (program n).c σ τ → cubeOrientation n hn c σ τ) ∧
      cubeRun n hn c s T ∧ 2 ^ n ≤ T := by sorry

end FriedmannCunningham
