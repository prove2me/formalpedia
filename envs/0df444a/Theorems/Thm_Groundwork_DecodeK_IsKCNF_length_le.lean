-- Prove2me | Theorems.Thm_Groundwork_DecodeK_IsKCNF_length_le
-- name    : Groundwork.DecodeK.IsKCNF.length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:54:55.723653+00:00
-- url     : https://prove2.me/theorems/cbb54f33-9984-4b6b-aae3-91e36af1fb82
-- title:
--   Is KCNF: length le
-- statement:
--   An instance on n variables has at most (2n+1)^k clauses, so its code is polynomially long.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L58-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean#L58-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_WidthK_Decode
import Theorems.Thm_Sat3_Is3CNF_length_le

set_option autoImplicit false
section
open Groundwork Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode

theorem Groundwork.DecodeK.IsKCNF.length_le {k n : ℕ} {φ : CNF n} (h : IsKCNF k φ) : φ.length ≤ (2 * n + 1) ^ k := by sorry
