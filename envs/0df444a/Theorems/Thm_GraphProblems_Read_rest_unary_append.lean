-- Prove2me | Theorems.Thm_GraphProblems_Read_rest_unary_append
-- name    : GraphProblems.Read.rest_unary_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:32:18.244369+00:00
-- url     : https://prove2.me/theorems/4b649111-7b83-4354-911f-5877974f42da
-- title:
--   Read: rest unary append
-- statement:
--   What follows the first ones and the zero that ends them in 1ᵐ0x is x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Read.lean#L32-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Read.lean#L32-L37

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

theorem GraphProblems.Read.rest_unary_append (m : ℕ) (x : List Bool) : rest (unary m ++ x) = x := by sorry
