-- Prove2me | Theorems.Thm_GeneralPieces_GenF_JmU_comm
-- name    : GeneralPieces.GenF.JmU_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:22.9841+00:00
-- url     : https://prove2.me/theorems/494b4ab9-3e98-44b7-9192-77d7d423c9c8
-- title:
--   Gen F: Jm U comm
-- statement:
--   J_n^-(u) and J_m^-(u) commute.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/DDComm.lean#L25-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/DDComm.lean#L25-L31

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

theorem GeneralPieces.GenF.JmU_comm (n m : ℕ) (p : Vu) : JmU n (JmU m p) = JmU m (JmU n p) := by sorry
