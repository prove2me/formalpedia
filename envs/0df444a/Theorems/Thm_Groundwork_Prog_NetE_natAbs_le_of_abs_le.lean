-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_natAbs_le_of_abs_le
-- name    : Groundwork.Prog.NetE.natAbs_le_of_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:31.028465+00:00
-- url     : https://prove2.me/theorems/96a20f6d-013e-4c11-b16f-a106eb24fe20
-- title:
--   Net E: nat Abs le of abs le
-- statement:
--   The Net E construction uses the nat Abs le of abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L37-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L37-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)

theorem Groundwork.Prog.NetE.natAbs_le_of_abs_le {z : ℤ} {n : ℕ} (h : |z| ≤ (n : ℤ)) : z.natAbs ≤ n := by sorry
