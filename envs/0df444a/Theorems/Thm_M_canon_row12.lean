-- Prove2me | Theorems.Thm_M_canon_row12
-- name    : M_canon_row12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:43:46.603955+00:00
-- url     : https://prove2.me/theorems/3c13edf4-e3ba-49dc-846f-ce573ffee7a8
-- title:
--   M canon row12: M canon row12
-- statement:
--   Lemma 1, block 12: the rows r_x^{12} go to the parabola (x², x, 0, 0).
--
--   Source: https://github.com/V-k-h/lisonek-salt-tilings/blob/8a4f1ed5aea2d3b4a1792201d819c168f3d75b71/code/lean/Conic.lean#L17-L21
-- source:
--   https://github.com/V-k-h/lisonek-salt-tilings/blob/8a4f1ed5aea2d3b4a1792201d819c168f3d75b71/code/lean/Conic.lean#L17-L21

import Mathlib
import Definitions.Def_LisonekSaltConic
set_option autoImplicit true
open Matrix
variable (p : ℕ) [Fact p.Prime]

theorem M_canon_row12 (n x : ZMod p) (h2 : (2 : ZMod p) ≠ 0) :
    (M_canon p n).mulVec (row12_orig p x) = ![x^2, x, 0, 0] := by sorry
