-- Prove2me | Theorems.Thm_HomologySpheresBoundBalls_hsbb_casson_harer_brieskorn
-- name    : HomologySpheresBoundBalls.hsbb_casson_harer_brieskorn
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T12:20:04.051559+00:00
-- url     : https://prove2.me/theorems/30b653c6-db5b-4fe1-822d-0c350ece7053
-- title:
--   Casson–Harer: Brieskorn families bounding contractible 4-manifolds
-- statement:
--   The following Brieskorn homology spheres bound compact smooth contractible 4-manifolds:
--
--   1. $\Sigma(p,\ ps-1,\ ps+1)$ for $p \ge 2$ even and $s$ odd;
--   2. $\Sigma(p,\ ps+1,\ ps+2)$ and $\Sigma(p,\ ps-1,\ ps-2)$ for $p \ge 3$ odd and $s \ge 1$.
--
--   These infinite families show that bounding a contractible (hence an integral homology) ball is common among Brieskorn spheres.
--
--   **Formalization Note.** The bounds $p \ge 2$, $p \ge 3$, $s \ge 1$ only exclude degenerate parameters and keep natural-number subtraction from truncating.
-- source:
--   Open Problem Garden, 'Which homology 3-spheres bound homology 4-balls?' (rybu, 2009), http://www.openproblemgarden.org/op/which_homology_3_spheres_bound_homology_4_balls

import Definitions.Def_hsbb_homology_balls
import Definitions.Def_hsbb_spaces

open scoped Manifold

namespace HomologySpheresBoundBalls

/-- (Casson–Harer) `Σ(p, ps-1, ps+1)` for `p` even and `s` odd, and `Σ(p, ps±1, ps±2)` for
`p` odd, bound smooth contractible 4-manifolds. -/
theorem hsbb_casson_harer_brieskorn :
    (∀ p s : ℕ, 2 ≤ p → Even p → Odd s →
      BoundsContractible (BrieskornSphere p (p * s - 1) (p * s + 1))) ∧
    (∀ p s : ℕ, 3 ≤ p → Odd p → 1 ≤ s →
      BoundsContractible (BrieskornSphere p (p * s + 1) (p * s + 2)) ∧
      BoundsContractible (BrieskornSphere p (p * s - 1) (p * s - 2))) := by sorry

end HomologySpheresBoundBalls
