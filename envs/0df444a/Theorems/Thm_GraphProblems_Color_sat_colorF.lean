-- Prove2me | Theorems.Thm_GraphProblems_Color_sat_colorF
-- name    : GraphProblems.Color.sat_colorF
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:36:35.983539+00:00
-- url     : https://prove2.me/theorems/715b2027-0f06-4f68-b874-b28d7f2d2b18
-- title:
--   Color: sat color F
-- statement:
--   What `colorF k n m` says.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L40-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L40-L72

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

theorem GraphProblems.Color.sat_colorF (k n : ℕ) (m : List Bool) (f : ℕ → Bool) : Sat f (colorF k n m) ↔
    (∀ v < n, ∃ c < k, f (v * k + c) = true) ∧
    (∀ v < n, ∀ c₁ < k, ∀ c₂ < k, c₁ < c₂ → f (v * k + c₁) = false ∨ f (v * k + c₂) = false) ∧
    ∀ u < n, ∀ v < n, adjB n m u v = true → ∀ c < k, f (u * k + c) = false ∨ f (v * k + c) = false := by sorry
