-- Prove2me | Theorems.Thm_MazurHuang_N19_covering_cubic_mod_twentyseven
-- name    : MazurHuang.N19.covering_cubic_mod_twentyseven
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:07.320073+00:00
-- url     : https://prove2.me/theorems/e342bcb1-678d-46c2-aa22-2ab8eb847c1e
-- title:
--   The cubic descent cover has no primitive zero modulo twenty-seven
-- statement:
--   Every zero modulo 27 of X³−3Y³+24Z³+3X²Y−9XY²+48X²Z+144Y²Z has all three coordinates divisible by three.
-- source:
--   Apache-2.0; https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580; XDelta19GoodDualDescent.lean:316-327

import Mathlib

theorem MazurHuang.N19.covering_cubic_mod_twentyseven :
    ∀ X Y Z : ZMod 27,
      X ^ 3 - 3 * Y ^ 3 + 24 * Z ^ 3 + 3 * X ^ 2 * Y -
          9 * X * Y ^ 2 + 48 * X ^ 2 * Z + 144 * Y ^ 2 * Z = 0 →
        ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) X = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Y = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Z = 0 := by sorry
