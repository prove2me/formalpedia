-- Prove2me | Theorems.Thm_GeneralPieces_Dual_aFam_eq
-- name    : GeneralPieces.Dual.aFam_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:53.712168+00:00
-- url     : https://prove2.me/theorems/e92e64cb-2420-4927-8b97-31634eb69958
-- title:
--   Dual: a Fam eq
-- statement:
--   a^μ is the product of the signs times ∏ y_{μ_i}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L334-L343
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L334-L343

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem GeneralPieces.Dual.aFam_eq (μ : List ℕ+) : aFam (μ : Multiset ℕ+) = (sgn μ : ℚ) • (μ.map y).prod := by sorry
