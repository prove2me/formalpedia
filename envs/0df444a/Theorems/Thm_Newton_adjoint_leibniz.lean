-- Prove2me | Theorems.Thm_Newton_adjoint_leibniz
-- name    : Newton.adjoint_leibniz
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:03:29.396794+00:00
-- url     : https://prove2.me/theorems/b8fe6684-67b6-4ca4-954a-e312417c1f9f
-- title:
--   Newton: adjoint leibniz
-- statement:
--   Leibniz rule for ad action (derivation property)
--
--   ad(A)([B, C]) = [ad(A)(B), C] + [B, ad(A)(C)]
--
--   This follows directly from the Jacobi identity.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L64-L67
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L64-L67

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}

theorem Newton.adjoint_leibniz (A B C : SuNAlgebra N) :
    adjointAd A ⁅B, C⁆ = ⁅adjointAd A B, C⁆ + ⁅B, adjointAd A C⁆ := by sorry
