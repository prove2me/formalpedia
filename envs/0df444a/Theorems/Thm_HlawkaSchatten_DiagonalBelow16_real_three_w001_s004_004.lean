-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w001_s004_004
-- name    : HlawkaSchatten.DiagonalBelow16.real_three_w001_s004_004
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T00:27:54.966768+00:00
-- url     : https://prove2.me/theorems/0058a19b-93dd-47e8-a328-cf594636115c
-- title:
--   Sharp real three-dimensional Hlawka bound for 2043/128 <= p <= 8173/512
-- statement:
--   For every real exponent $2043/128\le p\le 8173/512$, the sharp cyclic Hlawka constant $K_p$ satisfies
--   $$\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p\le K_p\bigl(2\|x\|_p+2\|y\|_p+2\|z\|_p-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p\bigr)$$
--   for all $x,y,z\in\mathbb R^3$. Here $K_p$ is the original cyclicConstant defined in the parent cutoff-16 mission. This complete small interval is separated from the larger interval solely to fit the platform verification time limit. It makes no claim about other exponents.
-- source:
--   Below-16 extension of the sharp diagonal Hlawka bound. Reuses the proved orientation and curvature criteria from the cutoff-16 mission, together with the separately proved coarse localization for this exponent window. The new finite scalar, total-norm barrier, contraction, and curvature comparisons are supplied explicitly. Subinterval 4 through 4, separated to fit the platform 300-second verification limit.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalBelow16.real_three_w001_s004_004 :
    ∀ p : ℝ, (2043/128 : ℝ) ≤ p → p ≤ (8173/512 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
