-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bra_tT_mul
-- name    : GeneralPieces.GenF.bra_tT_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:06:14.369096+00:00
-- url     : https://prove2.me/theorems/00f55d87-200e-4eff-a697-94cf9ba0b88c
-- title:
--   Gen F: bra t T mul
-- statement:
--   The coefficient of t^σ in t_k·f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L257-L261
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L257-L261

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

theorem GeneralPieces.GenF.bra_tT_mul (σ : Multiset ℕ) (k : ℕ) (f : Tv) : bra σ (tT k * f) = if k ∈ σ then bra (σ.erase k) f else 0 := by sorry
