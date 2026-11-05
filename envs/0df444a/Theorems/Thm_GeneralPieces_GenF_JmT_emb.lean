-- Prove2me | Theorems.Thm_GeneralPieces_GenF_JmT_emb
-- name    : GeneralPieces.GenF.JmT_emb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:06:45.635727+00:00
-- url     : https://prove2.me/theorems/c5eacb34-e88d-455b-b4c6-62bfbba53c65
-- title:
--   Gen F: Jm T emb
-- statement:
--   J_p^-(ω₁) kills the series without t_k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L71-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L71-L74

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

theorem GeneralPieces.GenF.JmT_emb (p : ℕ) (s : S) : JmT p (emb s) = 0 := by sorry
