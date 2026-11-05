-- Prove2me | Theorems.Thm_Groundwork_Prog_SatTopK_final_bound
-- name    : Groundwork.Prog.SatTopK.final_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:46:07.798138+00:00
-- url     : https://prove2.me/theorems/f31ab080-6cc7-4236-b8bd-5ab51dafe807
-- title:
--   Sat Top K: final bound
-- statement:
--   The sizes that occur in the proof of `sat_correct` are at most c·N^c, where N is the length of
--   the input plus 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Top/Sat.lean#L76-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Top/Sat.lean#L76-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_KSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_WidthK_Top_Sat
set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK
open Groundwork.Sparsify (leaves)

theorem Groundwork.Prog.SatTopK.final_bound (P₁ P₂ Q A N : ℕ) (h1 : 1 ≤ N) :
    P₂ * N ^ 3 + A * (P₁ * N ^ 2) ^ A + 4 ≤ cOf P₁ P₂ Q A * N ^ cOf P₁ P₂ Q A ∧
      Q * N ^ 2 + 3 ≤ cOf P₁ P₂ Q A * N ^ cOf P₁ P₂ Q A := by sorry
