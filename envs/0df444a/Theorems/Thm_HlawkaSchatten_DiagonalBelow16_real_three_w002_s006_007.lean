-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w002_s006_007
-- name    : HlawkaSchatten.DiagonalBelow16.real_three_w002_s006_007
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-26T23:39:54.217864+00:00
-- url     : https://prove2.me/theorems/fd25c211-3e6c-41a0-9506-b074416fd197
-- title:
--   Sharp real three-dimensional Hlawka bound for 4091/256 <= p <= 1023/64
-- statement:
--   For every real exponent $4091/256\le p\le 1023/64$, the sharp cyclic Hlawka constant $K_p$ satisfies
--   $$\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p\le K_p\bigl(2\|x\|_p+2\|y\|_p+2\|z\|_p-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p\bigr)$$
--   for all $x,y,z\in\mathbb R^3$. Here $K_p$ is the original cyclicConstant defined in the parent cutoff-16 mission. This complete small interval is separated from the larger interval solely to fit the platform verification time limit. It makes no claim about other exponents.
-- source:
--   Below-16 extension of the sharp diagonal Hlawka bound. Reuses the proved orientation and curvature criteria from the cutoff-16 mission, together with the separately proved coarse localization for this exponent window. The new finite scalar, total-norm barrier, contraction, and curvature comparisons are supplied explicitly. Subinterval 6 through 7, separated to fit the platform 300-second verification limit.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalBelow16.real_three_w002_s006_007 :
    ∀ p : ℝ, (4091/256 : ℝ) ≤ p → p ≤ (1023/64 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
