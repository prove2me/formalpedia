-- Prove2me | Theorems.Thm_Groundwork_Prog_abs_value_le
-- name    : Groundwork.Prog.abs_value_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:29:48.923529+00:00
-- url     : https://prove2.me/theorems/53d8c187-2efb-4805-80c1-ae099c458627
-- title:
--   Prog: abs value le
-- statement:
--   A network on the nodes J with at most 2^P states a node and all weights W and interactions Ψ at
--   most 2^B in absolute
--   value (part of `Sized P B`) has a value Z with |Z| ≤ 2^{|J|(P+B) + |J|²B}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridLoop.lean#L25-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridLoop.lean#L25-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_GridLoop
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped

theorem Groundwork.Prog.abs_value_le {J σ τ : Type} [Fintype J] [LinearOrder J] (N : Network J σ τ) {P B : ℕ}
    (h : N.Sized P B) : |N.value| ≤ 2 ^ (Fintype.card J * (P + B) + Fintype.card J * Fintype.card J * B) := by sorry
