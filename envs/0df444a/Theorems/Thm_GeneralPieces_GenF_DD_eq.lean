-- Prove2me | Theorems.Thm_GeneralPieces_GenF_DD_eq
-- name    : GeneralPieces.GenF.DD_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:30.18258+00:00
-- url     : https://prove2.me/theorems/4610bd69-6ace-4a49-b380-01501fb3329c
-- title:
--   Gen F: DD eq
-- statement:
--   The Gen F construction uses the DD eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/DDComm.lean#L42-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/DDComm.lean#L42-L48

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

theorem GeneralPieces.GenF.DD_eq (rd : Bool) (i : X) : DD rd i = 0 ∨ ∃ n, DD rd i = JmT n := by sorry
