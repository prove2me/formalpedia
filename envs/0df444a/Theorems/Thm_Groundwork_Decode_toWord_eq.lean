-- Prove2me | Theorems.Thm_Groundwork_Decode_toWord_eq
-- name    : Groundwork.Decode.toWord_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:27:26.901368+00:00
-- url     : https://prove2.me/theorems/89785f7e-ed67-47c4-adc4-99ffdf2b837f
-- title:
--   Decode: to Word eq
-- statement:
--   The Decode construction uses the to Word eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L59-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean#L59-L67

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

theorem Groundwork.Decode.toWord_eq (ℓ y : ℕ) : toWord ℓ y = (List.range ℓ).map y.testBit := by sorry
