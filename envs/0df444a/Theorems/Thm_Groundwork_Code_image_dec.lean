-- Prove2me | Theorems.Thm_Groundwork_Code_image_dec
-- name    : Groundwork.Code.image_dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:56:45.354986+00:00
-- url     : https://prove2.me/theorems/b425da56-747c-46dc-834d-61f4066bc1af
-- title:
--   Code: image dec
-- statement:
--   The Code construction uses the image dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Code.lean#L38-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Code.lean#L38-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_StepMachines_Math_Code
set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}

theorem Groundwork.Code.image_dec [DecidableEq X] (c : Code S n) : c.D.image c.dec = S := by sorry
