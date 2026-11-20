-- Prove2me | Theorems.Thm_M_canon_det
-- name    : M_canon_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:45:24.543109+00:00
-- url     : https://prove2.me/theorems/7f66f0c4-5da8-4f75-9743-18b9fdd551ad
-- title:
--   M canon det: M canon det
-- statement:
--   M_canon is invertible: det = -2.
--
--   Source: https://github.com/V-k-h/lisonek-salt-tilings/blob/8a4f1ed5aea2d3b4a1792201d819c168f3d75b71/code/lean/Conic.lean#L31-L33
-- source:
--   https://github.com/V-k-h/lisonek-salt-tilings/blob/8a4f1ed5aea2d3b4a1792201d819c168f3d75b71/code/lean/Conic.lean#L31-L33

import Mathlib
import Definitions.Def_LisonekSaltConic
set_option autoImplicit true
open Matrix
variable (p : ℕ) [Fact p.Prime]

theorem M_canon_det (n : ZMod p) : (M_canon p n).det = -2 := by sorry
