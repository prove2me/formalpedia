-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w001_s006_007
-- name    : HlawkaSchatten.DiagonalBelow16.real_three_w001_s006_007
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-26T23:39:50.130378+00:00
-- url     : https://prove2.me/theorems/f97cf3f1-74ed-41ee-8738-8ca66846bf0f
-- title:
--   Sharp real three-dimensional Hlawka bound for 4087/256 <= p <= 511/32
-- statement:
--   For every real exponent $4087/256\le p\le 511/32$, the sharp cyclic Hlawka constant $K_p$ satisfies
--   $$\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p\le K_p\bigl(2\|x\|_p+2\|y\|_p+2\|z\|_p-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p\bigr)$$
--   for all $x,y,z\in\mathbb R^3$. Here $K_p$ is the original cyclicConstant defined in the parent cutoff-16 mission. This complete small interval is separated from the larger interval solely to fit the platform verification time limit. It makes no claim about other exponents.
-- source:
--   Below-16 extension of the sharp diagonal Hlawka bound. Reuses the proved orientation and curvature criteria from the cutoff-16 mission, together with the separately proved coarse localization for this exponent window. The new finite scalar, total-norm barrier, contraction, and curvature comparisons are supplied explicitly. Subinterval 6 through 7, separated to fit the platform 300-second verification limit.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalBelow16.real_three_w001_s006_007 :
    ∀ p : ℝ, (4087/256 : ℝ) ≤ p → p ≤ (511/32 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
