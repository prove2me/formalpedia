-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w001_s000_000
-- name    : HlawkaSchatten.DiagonalBelow16.real_three_w001_s000_000
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T00:27:48.019543+00:00
-- url     : https://prove2.me/theorems/50a7c01d-7171-4f43-a94d-34d034b65526
-- title:
--   Sharp real three-dimensional Hlawka bound for 1021/64 <= p <= 8169/512
-- statement:
--   For every real exponent $1021/64\le p\le 8169/512$, the sharp cyclic Hlawka constant $K_p$ satisfies
--   $$\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p\le K_p\bigl(2\|x\|_p+2\|y\|_p+2\|z\|_p-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p\bigr)$$
--   for all $x,y,z\in\mathbb R^3$. Here $K_p$ is the original cyclicConstant defined in the parent cutoff-16 mission. This complete small interval is separated from the larger interval solely to fit the platform verification time limit. It makes no claim about other exponents.
-- source:
--   Below-16 extension of the sharp diagonal Hlawka bound. Reuses the proved orientation and curvature criteria from the cutoff-16 mission, together with the separately proved coarse localization for this exponent window. The new finite scalar, total-norm barrier, contraction, and curvature comparisons are supplied explicitly. Subinterval 0 through 0, separated to fit the platform 300-second verification limit.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalBelow16.real_three_w001_s000_000 :
    ∀ p : ℝ, (1021/64 : ℝ) ≤ p → p ≤ (8169/512 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
