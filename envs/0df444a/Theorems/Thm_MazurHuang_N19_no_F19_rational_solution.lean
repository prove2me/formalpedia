-- Prove2me | Theorems.Thm_MazurHuang_N19_no_F19_rational_solution
-- name    : MazurHuang.N19.no_F19_rational_solution
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T14:56:19.44943+00:00
-- url     : https://prove2.me/theorems/3b3ef3ef-c3ba-4c11-82ec-4a92c55f0d31
-- title:
--   The order-nineteen Tate polynomial has no nondegenerate rational zero
-- statement:
--   For rational numbers $b,c$ with $b\ne0$, the order-nineteen Tate division factor satisfies $F_{19}(b,c)\ne0$. Thus the nondegenerate Tate locus required by a rational point of order nineteen is empty.
-- source:
--   https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580

import Mathlib
import Definitions.Def_MazurHuang_NineteenTatePolynomial

theorem MazurHuang.N19.no_F19_rational_solution (b c : ℚ) (hb : b ≠ 0) : MazurProof.TateNFDivision.F19 b c ≠ 0 := by sorry
