-- Prove2me | Theorems.Thm_GeneralPieces_GenF_JmT_JpV
-- name    : GeneralPieces.GenF.JmT_JpV
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:06:39.429471+00:00
-- url     : https://prove2.me/theorems/ec1c4002-101e-4ccd-ad67-023f7a059982
-- title:
--   Gen F: Jm T Jp V
-- statement:
--   J_p^-(ω₁) applied to J_q^+(ω₂) is the sum over k in the display for κ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L37-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean#L37-L68

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

theorem GeneralPieces.GenF.JmT_JpV (p q : ℕ) : JmT p (JpV q) = emb (kapS p q) := by sorry
