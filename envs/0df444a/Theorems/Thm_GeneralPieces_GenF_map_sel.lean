-- Prove2me | Theorems.Thm_GeneralPieces_GenF_map_sel
-- name    : GeneralPieces.GenF.map_sel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:33.537234+00:00
-- url     : https://prove2.me/theorems/7583964d-0866-4c0e-95cb-b8608650ce01
-- title:
--   Gen F: map sel
-- statement:
--   A map φ with φ 0 = 0 may be applied to the values.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L68-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L68-L70

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

theorem GeneralPieces.GenF.map_sel {R R' : Type} [Zero R] [Zero R'] (φ : R → R') (h0 : φ 0 = 0) (rd : Bool) (f g : ℕ → R) (x : X) :
    φ (sel rd f g x) = sel rd (fun n => φ (f n)) (fun n => φ (g n)) x := by sorry
