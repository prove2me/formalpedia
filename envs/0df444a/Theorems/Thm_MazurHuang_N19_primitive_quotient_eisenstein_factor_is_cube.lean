-- Prove2me | Theorems.Thm_MazurHuang_N19_primitive_quotient_eisenstein_factor_is_cube
-- name    : MazurHuang.N19.primitive_quotient_eisenstein_factor_is_cube
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:47.818183+00:00
-- url     : https://prove2.me/theorems/9604f849-d355-471c-95c2-8e0f49c32845
-- title:
--   The primitive quotient Eisenstein factor is a cube
-- statement:
--   For coprime primitive quotient coordinates with positive denominator, the Eisenstein factor n−√−3·d(24m+12d²) is a cube in the Eisenstein integers. The proof extracts a unit times a cube and rules out the two nontrivial unit classes by the cubic covering congruence.
-- source:
--   Apache-2.0; https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580; XDelta19GoodDualDescent.lean:30-314,342-524; RationalPointsX135Descent.lean:3-136,569-576,656-858,874-911,1113-1173

import Mathlib
import Definitions.Def_MazurHuang_EisensteinDescent35

theorem MazurHuang.N19.primitive_quotient_eisenstein_factor_is_cube {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 - 3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2) :
    ∃ B : MazurHuang.EisensteinDescent35.N35O3,
      (n : MazurHuang.EisensteinDescent35.N35O3) -
        MazurHuang.EisensteinDescent35.n35SqrtNegThree *
          (d * (24 * m + 12 * d ^ 2) : ℤ) = B ^ 3 := by sorry
