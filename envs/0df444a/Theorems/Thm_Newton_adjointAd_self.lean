-- Prove2me | Theorems.Thm_Newton_adjointAd_self
-- name    : Newton.adjointAd.self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:34:42.113804+00:00
-- url     : https://prove2.me/theorems/38b56ab6-627a-4ffb-9b91-54a19ea51dfc
-- title:
--   adjoint Ad: self
-- statement:
--   ad action on self is zero: ad(A)(A) = 0
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L47-L49
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L47-L49

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAd

theorem Newton.adjointAd.self (A : SuNAlgebra N) : adjointAd A A = 0 := by sorry
