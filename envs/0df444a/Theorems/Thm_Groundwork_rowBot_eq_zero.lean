-- Prove2me | Theorems.Thm_Groundwork_rowBot_eq_zero
-- name    : Groundwork.rowBot_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:11.227373+00:00
-- url     : https://prove2.me/theorems/3cb48fe3-862c-4b49-b775-fe91953f4cf8
-- title:
--   Groundwork: row Bot eq zero
-- statement:
--   With fewer than i singlets in β, every set of i positions has one where β is no singlet, and the
--   term vanishes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L114-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L114-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Cross_Cuts
set_option autoImplicit false
section
section
open Groundwork
open Finset

theorem Groundwork.rowBot_eq_zero {n i : ℕ} {β : Fin n → Bell} (h : singlets β < i) (p q : Bits n) : rowBit.Bot i β p q = 0 := by sorry
