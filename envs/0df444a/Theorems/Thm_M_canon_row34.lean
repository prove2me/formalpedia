-- Prove2me | Theorems.Thm_M_canon_row34
-- name    : M_canon_row34
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:44:19.947145+00:00
-- url     : https://prove2.me/theorems/7b233fa9-7559-4c3b-95ec-6a3fda66e1e6
-- title:
--   M canon row34: M canon row34
-- statement:
--   Lemma 1, block 34: the rows r_y^{34} go to the parabola (y²/n, 0, 1, y).
--
--   Source: https://github.com/V-k-h/lisonek-salt-tilings/blob/8a4f1ed5aea2d3b4a1792201d819c168f3d75b71/code/lean/Conic.lean#L24-L28
-- source:
--   https://github.com/V-k-h/lisonek-salt-tilings/blob/8a4f1ed5aea2d3b4a1792201d819c168f3d75b71/code/lean/Conic.lean#L24-L28

import Mathlib
import Definitions.Def_LisonekSaltConic
set_option autoImplicit true
open Matrix
variable (p : ℕ) [Fact p.Prime]

theorem M_canon_row34 (n y : ZMod p) (h2 : (2 : ZMod p) ≠ 0) (hn : n ≠ 0) :
    (M_canon p n).mulVec (row34_orig p n y) = ![y^2 * n⁻¹, 0, 1, y] := by sorry
