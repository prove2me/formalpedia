-- Prove2me | Theorems.Thm_Groundwork_Decode_satN_toN
-- name    : Groundwork.Decode.satN_toN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:26:31.590601+00:00
-- url     : https://prove2.me/theorems/8f7ebf37-50de-4ab5-b0e4-0aad382b0474
-- title:
--   Decode: sat N to N
-- statement:
--   Satisfiability does not depend on how variables are named.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L189-L200
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L189-L200

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Prog_Decode
set_option autoImplicit false
section
open Groundwork Groundwork.Decode
open Sat3

theorem Groundwork.Decode.satN_toN {n : ℕ} (φ : CNF n) : SatN (toN φ) ↔ Satisfiable φ := by sorry
