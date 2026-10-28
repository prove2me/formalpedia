-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s001_001
-- name    : HlawkaSchatten.DiagonalBelow16.real_three_w003_s001_001
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T00:35:49.213446+00:00
-- url     : https://prove2.me/theorems/93dcb96c-0bf3-46b6-9210-6274e4751fe0
-- title:
--   Sharp real three-dimensional Hlawka bound for 8185/512 <= p <= 4093/256
-- statement:
--   For every real exponent $8185/512\le p\le 4093/256$, the sharp cyclic Hlawka constant $K_p$ satisfies
--   $$\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p\le K_p\bigl(2\|x\|_p+2\|y\|_p+2\|z\|_p-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p\bigr)$$
--   for all $x,y,z\in\mathbb R^3$. Here $K_p$ is the original cyclicConstant defined in the parent cutoff-16 mission. This complete small interval is separated from the larger interval solely to fit the platform verification time limit. It makes no claim about other exponents.
-- source:
--   Below-16 extension of the sharp diagonal Hlawka bound. Reuses the proved orientation and curvature criteria from the cutoff-16 mission, together with the separately proved coarse localization for this exponent window. The new finite scalar, total-norm barrier, contraction, and curvature comparisons are supplied explicitly. Subinterval 1 through 1, separated to fit the platform 300-second verification limit.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalBelow16.real_three_w003_s001_001 :
    ∀ p : ℝ, (8185/512 : ℝ) ≤ p → p ≤ (4093/256 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
