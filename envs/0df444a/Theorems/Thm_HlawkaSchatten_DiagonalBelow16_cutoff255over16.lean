-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalBelow16_cutoff255over16
-- name    : HlawkaSchatten.DiagonalBelow16.cutoff255over16
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-26T23:39:48.11747+00:00
-- url     : https://prove2.me/theorems/b050e074-adbd-4283-b026-08e8a8ab5f19
-- title:
--   Sharp diagonal Hlawka constants for every real p >= 255/16
-- statement:
--   For every real exponent $p\ge255/16$, the cyclic constant
--   $$K_p=\sup_{1/2\le t\le2}
--   \frac{3(t^p+2)^{1/p}-3^{1/p}|2-t|}
--   {6(t^p+2)^{1/p}-3(2|1-t|^p+2^p)^{1/p}}$$
--   is the least constant $C$ such that
--   $$\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p
--   \le C\bigl(2\|x\|_p+2\|y\|_p+2\|z\|_p-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p\bigr)$$
--   holds for all dimensions $n$ and all $x,y,z\in\mathbb C^n$.
--   This lowers the proved cutoff from 16 to $255/16=15.9375$. It does not assert that this cutoff is optimal or settle the range $2<p<255/16$.
-- source:
--   Original below-16 extension of the Prove2Me sharp diagonal Hlawka campaign. The new finite band [255/16,16] uses the generic orientation and convexity criteria from the accepted cutoff-16 proof, with new scalar, localization, barrier, contraction and curvature certificates. Parent campaign: https://prove2.me/theorems/7fe6f02d-65e5-4c21-9796-c83889b29b9d .

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalBelow16.cutoff255over16 :
    ∀ p : ℝ, (255/16 : ℝ) ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by sorry
