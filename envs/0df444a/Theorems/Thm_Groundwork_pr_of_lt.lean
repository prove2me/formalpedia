-- Prove2me | Theorems.Thm_Groundwork_pr_of_lt
-- name    : Groundwork.pr_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:27:59.464437+00:00
-- url     : https://prove2.me/theorems/6bd01cd2-52f4-4b78-8571-18a86d91d5c8
-- title:
--   Groundwork: pr of lt
-- statement:
--   Both orders of a pair a < b have the name (a, b).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L66-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L66-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}

theorem Groundwork.pr_of_lt [LinearOrder J] {a b : J} (h : a < b) : pr a b = (a, b) ∧ pr b a = (a, b) := by sorry
