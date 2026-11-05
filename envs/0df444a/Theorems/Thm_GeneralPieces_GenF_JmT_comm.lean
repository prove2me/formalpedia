-- Prove2me | Theorems.Thm_GeneralPieces_GenF_JmT_comm
-- name    : GeneralPieces.GenF.JmT_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:24.50516+00:00
-- url     : https://prove2.me/theorems/55e570f8-7ee7-4ed6-893d-62d2ee1dbb94
-- title:
--   Gen F: Jm T comm
-- statement:
--   The Gen F construction uses the Jm T comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/DDComm.lean#L33-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/DDComm.lean#L33-L33

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

theorem GeneralPieces.GenF.JmT_comm (n m : ℕ) (f : Tv) : JmT n (JmT m f) = JmT m (JmT n f) := by sorry
