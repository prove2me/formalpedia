-- Prove2me | Theorems.Thm_GraphProblems_Color_asg_injective
-- name    : GraphProblems.Color.asg_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:41:53.504407+00:00
-- url     : https://prove2.me/theorems/3d6ebace-b26e-457a-a0c3-869f2db622a2
-- title:
--   Color: asg injective
-- statement:
--   Different maps have different assignments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L100-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L100-L105

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_Color
set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Color
open Blocks

theorem GraphProblems.Color.asg_injective {n k : ℕ} : Function.Injective (asg : (Fin n → Fin k) → Fin (n * k) → Bool) := by sorry
