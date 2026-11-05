-- Prove2me | Theorems.Thm_Groundwork_sum_range_eq_list
-- name    : Groundwork.sum_range_eq_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:29:15.165042+00:00
-- url     : https://prove2.me/theorems/bd18a48f-770c-4c82-b042-3e212f90cd88
-- title:
--   Groundwork: sum range eq list
-- statement:
--   A sum over `Finset.range` as the sum of a list, the form in which it is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Digits.lean#L24-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Digits.lean#L24-L27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_ToTuring_Poly_Digits
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open Groundwork
variable {α : Type} [Enc α]

theorem Groundwork.sum_range_eq_list (R : ℕ) (f : ℕ → ℕ) : ∑ q ∈ Finset.range R, f q = ((List.range R).map f).sum := by sorry
