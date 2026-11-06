-- Prove2me | Theorems.Thm_GraphProblems_Color_exists_mem_pair
-- name    : GraphProblems.Color.exists_mem_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:41:33.248175+00:00
-- url     : https://prove2.me/theorems/7c4c183c-c799-46da-bcc8-02102a10990e
-- title:
--   Color: exists mem pair
-- statement:
--   A clause of two literals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L36-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L36-L37

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

theorem GraphProblems.Color.exists_mem_pair (f : ℕ → Bool) (l₁ l₂ : ℕ × Bool) : (∃ l ∈ [l₁, l₂], f l.1 = l.2) ↔ f l₁.1 = l₁.2 ∨ f l₂.1 = l₂.2 := by sorry
