-- Prove2me | Theorems.Thm_MazurHuang_N19_exists_tate_parameters_of_order_nineteen
-- name    : MazurHuang.N19.exists_tate_parameters_of_order_nineteen
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T14:56:41.125191+00:00
-- url     : https://prove2.me/theorems/513fbb87-3e42-4087-bda9-33129d179fc2
-- title:
--   An order-nineteen point supplies nondegenerate Tate parameters
-- statement:
--   Let $E$ be an elliptic curve over $\mathbb{Q}$ and let $P$ be a rational point with additive order nineteen. There exist rational Tate parameters $b,c$ with $b\ne0$ and $F_{19}(b,c)=0$, where $F_{19}$ is the explicit order-nineteen division factor.
-- source:
--   https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580

import Mathlib
import Definitions.Def_MazurHuang_NineteenTatePolynomial
open scoped WeierstrassCurve.Affine

theorem MazurHuang.N19.exists_tate_parameters_of_order_nineteen (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 19) :
    ∃ b c : ℚ, b ≠ 0 ∧ MazurProof.TateNFDivision.F19 b c = 0 := by sorry
