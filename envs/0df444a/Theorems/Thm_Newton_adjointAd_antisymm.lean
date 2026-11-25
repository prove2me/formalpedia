-- Prove2me | Theorems.Thm_Newton_adjointAd_antisymm
-- name    : Newton.adjointAd.antisymm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:02:54.670299+00:00
-- url     : https://prove2.me/theorems/e5c87482-477b-42e3-b122-0b5fc72132ab
-- title:
--   adjoint Ad: antisymm
-- statement:
--   Antisymmetry of ad action: ad(A)(B) = -ad(B)(A)
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L52-L54
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L52-L54

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAd

theorem Newton.adjointAd.antisymm (A B : SuNAlgebra N) : adjointAd A B = -adjointAd B A := by sorry
