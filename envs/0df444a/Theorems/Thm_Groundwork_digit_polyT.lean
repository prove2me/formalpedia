-- Prove2me | Theorems.Thm_Groundwork_digit_polyT
-- name    : Groundwork.digit_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:30:04.792511+00:00
-- url     : https://prove2.me/theorems/33d3e91b-733c-4912-a464-18bba8fb3b32
-- title:
--   Groundwork: digit poly T
-- statement:
--   The digit number q of y in base n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Digits.lean#L30-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Digits.lean#L30-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_ToTuring_Poly_Digits
set_option autoImplicit false
section
section
open Groundwork
variable {α : Type} [Enc α]

theorem Groundwork.digit_polyT {n y q : α → ℕ} (h1 : PolyT n) (h2 : PolyT y) (h3 : PolyT q) :
    PolyT fun x => Prog.digit (n x) (y x) (q x) := by sorry
