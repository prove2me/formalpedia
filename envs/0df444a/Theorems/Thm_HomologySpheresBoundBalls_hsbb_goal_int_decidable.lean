-- Prove2me | Theorems.Thm_HomologySpheresBoundBalls_hsbb_goal_int_decidable
-- name    : HomologySpheresBoundBalls.hsbb_goal_int_decidable
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T12:21:29.219595+00:00
-- url     : https://prove2.me/theorems/a04ed30d-2c16-45d2-a413-76f7d06d0dfa
-- title:
--   Bounding an integral homology ball is decidable
-- statement:
--   Present a closed 3-manifold by a finite simplicial complex $K$: a list of simplices, each a list of vertex labels in $\mathbb N$, with geometric realization $|K|$. There is a computable function $f$ from such lists to $\{\mathtt{true}, \mathtt{false}\}$ such that for every $K$ whose realization is an integral homology 3-sphere,
--   $$f(K) = \mathtt{true} \iff |K| \text{ bounds a smooth integral homology 4-ball}.$$
--
--   This formalizes the question *is there a complete and computable set of invariants that can determine which homology 3-spheres bound homology 4-balls?* A complete computable invariant yields such a decision procedure, and conversely $f$ is itself a complete computable invariant. The problem is open; a proof of the negation would also settle it.
--
--   **Formalization Note.** "Computable" is Mathlib's `Computable` (partial recursive, total). The behaviour of $f$ on complexes that are not integral homology 3-spheres is unconstrained.
-- source:
--   Open Problem Garden, 'Which homology 3-spheres bound homology 4-balls?' (rybu, 2009), http://www.openproblemgarden.org/op/which_homology_3_spheres_bound_homology_4_balls

import Definitions.Def_hsbb_homology_balls
import Definitions.Def_hsbb_spaces

open scoped Manifold

namespace HomologySpheresBoundBalls

/-- **Goal.** There is an algorithm which, given a finite simplicial complex `K` whose
realization is an integral homology 3-sphere, decides whether `|K|` bounds a smooth
integral homology 4-ball. -/
theorem hsbb_goal_int_decidable :
    ∃ f : List (List ℕ) → Bool, Computable f ∧
      ∀ K : List (List ℕ), IsIntHomology3Sphere (realization K) →
        (f K = true ↔ BoundsIntHomologyBall (realization K)) := by sorry

end HomologySpheresBoundBalls
