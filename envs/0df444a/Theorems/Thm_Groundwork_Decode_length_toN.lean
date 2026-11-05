-- Prove2me | Theorems.Thm_Groundwork_Decode_length_toN
-- name    : Groundwork.Decode.length_toN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:26:24.717175+00:00
-- url     : https://prove2.me/theorems/885bf979-b0ee-4c49-98fa-d1462870cd50
-- title:
--   Decode: length to N
-- statement:
--   The Decode construction uses the length to N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L206-L206
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L206-L206

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

theorem Groundwork.Decode.length_toN {n : ℕ} (φ : CNF n) : (toN φ).length = φ.length := by sorry
