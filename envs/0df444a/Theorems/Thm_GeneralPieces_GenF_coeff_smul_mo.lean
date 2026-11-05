-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_smul_mo
-- name    : GeneralPieces.GenF.coeff_smul_mo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:59.599276+00:00
-- url     : https://prove2.me/theorems/35d1cf0c-9133-4671-9664-84a18bff635e
-- title:
--   Gen F: coeff smul mo
-- statement:
--   q·u^x·v^y, coefficient by coefficient in v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L279-L284
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L279-L284

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

theorem GeneralPieces.GenF.coeff_smul_mo (q : ℚ) (x y y' : ℤ) : (q • mo x y).coeff y' = if y' = y then C q * T x else 0 := by sorry
