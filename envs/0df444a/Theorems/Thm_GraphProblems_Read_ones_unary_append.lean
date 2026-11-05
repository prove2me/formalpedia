-- Prove2me | Theorems.Thm_GraphProblems_Read_ones_unary_append
-- name    : GraphProblems.Read.ones_unary_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:32:07.523386+00:00
-- url     : https://prove2.me/theorems/0e764308-d0ba-482b-a6a7-bfdb8c054bcd
-- title:
--   Read: ones unary append
-- statement:
--   The number of ones at the start of 1ᵐ0x is m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Read.lean#L24-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Read.lean#L24-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Read
set_option autoImplicit false
section
section
open GraphProblems
open GraphProblems.Read

theorem GraphProblems.Read.ones_unary_append (m : ℕ) (x : List Bool) : ones (unary m ++ x) = m := by sorry
