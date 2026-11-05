-- Prove2me | Theorems.Thm_GeneralPieces_GenF_JmU_C_mul_X
-- name    : GeneralPieces.GenF.JmU_C_mul_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:06:42.275727+00:00
-- url     : https://prove2.me/theorems/7ce3f837-736f-4a1b-bfff-736dff4d6752
-- title:
--   Gen F: Jm U C mul X
-- statement:
--   J_p^-(ω₁) on a multiple of t_k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L31-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L31-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
open MvPowerSeries hiding C X

theorem GeneralPieces.GenF.JmU_C_mul_X (p : ℕ) (c : Lu) (k : ℕ) :
    JmU p (MvPolynomial.C c * MvPolynomial.X k) = MvPolynomial.C (c * (C ((k : ℚ) * (bet p (-(k : ℤ)) : ℚ)) * T (-(k : ℤ) - p))) := by sorry
