-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bra_prod_tT
-- name    : GeneralPieces.GenF.bra_prod_tT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:07.32569+00:00
-- url     : https://prove2.me/theorems/50f6db46-39b2-454d-9c0c-11fe9d8af6ce
-- title:
--   Gen F: bra prod t T
-- statement:
--   The coefficient of t^σ in the monomial t^σ'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L336-L346
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L336-L346

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

theorem GeneralPieces.GenF.bra_prod_tT (σ σ' : Multiset ℕ) : bra σ ((σ'.map tT).prod) = if σ = σ' then 1 else 0 := by sorry
