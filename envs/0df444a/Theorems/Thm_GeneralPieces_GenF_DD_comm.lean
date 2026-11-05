-- Prove2me | Theorems.Thm_GeneralPieces_GenF_DD_comm
-- name    : GeneralPieces.GenF.DD_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:41.704173+00:00
-- url     : https://prove2.me/theorems/971e99da-0fd9-408a-9dfb-f1072b3e78b9
-- title:
--   Gen F: DD comm
-- statement:
--   The operators that stand beside the variables in A⁻ commute.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/DDComm.lean#L51-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/DDComm.lean#L51-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_GenF_DDComm
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson

theorem GeneralPieces.GenF.DD_comm (rd : Bool) (i j : X) (a : Tv) : DD rd i (DD rd j a) = DD rd j (DD rd i a) := by sorry
