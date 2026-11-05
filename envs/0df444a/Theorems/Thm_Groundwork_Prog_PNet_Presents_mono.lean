-- Prove2me | Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
-- name    : Groundwork.Prog.PNet.Presents.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:25:00.745641+00:00
-- url     : https://prove2.me/theorems/3ffba9ad-a13a-4ee8-96a4-2f7b86f3c6a4
-- title:
--   Presents: mono
-- statement:
--   Presents is monotone in the bounds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridDefs.lean#L91-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridDefs.lean#L91-L94

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Math_GridArith
import Definitions.Def_StepMachines_Prog_GridDefs
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped

theorem Groundwork.Prog.PNet.Presents.mono {C : Type} {Np : PNet C} {c : C} {g : ℕ} {N : Network (Fin g) (List Bool) (List Bool)}
    {t t' S S' : ℕ} (h : Np.Presents c N t S) (ht : t ≤ t') (hS : S ≤ S') : Np.Presents c N t' S' := by sorry
