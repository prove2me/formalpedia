-- Prove2me | Theorems.Thm_GeneralPieces_GenF_xi_or_xo
-- name    : GeneralPieces.GenF.xi_or_xo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:32:18.290891+00:00
-- url     : https://prove2.me/theorems/3a222f90-22d0-4071-a7de-8381b7539a84
-- title:
--   Gen F: xi or xo
-- statement:
--   Every variable belongs to the inner or to the outer family.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L64-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L64-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

theorem GeneralPieces.GenF.xi_or_xo (rd : Bool) (x : X) : (∃ n, x = xi rd n) ∨ ∃ n, x = xo rd n := by sorry
