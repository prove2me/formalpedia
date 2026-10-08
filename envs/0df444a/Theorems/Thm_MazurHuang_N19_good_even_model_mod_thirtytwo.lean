-- Prove2me | Theorems.Thm_MazurHuang_N19_good_even_model_mod_thirtytwo
-- name    : MazurHuang.N19.good_even_model_mod_thirtytwo
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:08.153978+00:00
-- url     : https://prove2.me/theorems/b25ba1cd-c4a0-4263-acc8-bfd3a92a3be1
-- title:
--   Two-adic normalization of the even good-model branch
-- statement:
--   If the good integral equation holds modulo 32 with an even horizontal numerator and odd denominator, then the numerator is zero modulo four and both flex factors are zero modulo eight.
-- source:
--   Apache-2.0; https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580; XDelta19GoodDescent.lean:27-46

import Mathlib

theorem MazurHuang.N19.good_even_model_mod_thirtytwo :
    ∀ A B C : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) A = 0 →
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) B ≠ 0 →
      C ^ 2 = A ^ 3 + 64 * A ^ 2 * B ^ 2 + 1216 * A * B ^ 4 +
          5776 * B ^ 6 →
      ZMod.castHom (show 4 ∣ 32 by norm_num) (ZMod 4) A = 0 ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C -
            8 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B -
            76 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C +
            8 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B +
            76 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) := by sorry
