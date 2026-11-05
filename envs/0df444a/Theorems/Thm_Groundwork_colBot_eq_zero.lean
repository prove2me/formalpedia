-- Prove2me | Theorems.Thm_Groundwork_colBot_eq_zero
-- name    : Groundwork.colBot_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:11.958995+00:00
-- url     : https://prove2.me/theorems/14393b8e-d649-4a65-959d-5f6d09b4ba65
-- title:
--   Groundwork: col Bot eq zero
-- statement:
--   With more than i states other than Φ⁺ in β, every set of i positions misses one of them, and the
--   term vanishes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L130-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L130-L144

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

theorem Groundwork.colBot_eq_zero {n i : ℕ} {β : Fin n → Bell} (h : i < others β) (p q : Bits n) : colBit.Bot i β p q = 0 := by sorry
