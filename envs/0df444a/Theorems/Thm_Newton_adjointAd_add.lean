-- Prove2me | Theorems.Thm_Newton_adjointAd_add
-- name    : Newton.adjointAd.add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:02:29.69533+00:00
-- url     : https://prove2.me/theorems/853cc315-902a-4cd6-971e-f5f8b19f5d18
-- title:
--   adjoint Ad: add
-- statement:
--   ad action preserves addition: ad(A)(B + C) = ad(A)(B) + ad(A)(C)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L20-L23
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L20-L23

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAd

theorem Newton.adjointAd.add (A B C : SuNAlgebra N) :
    adjointAd A (B + C) = adjointAd A B + adjointAd A C := by sorry
