-- Prove2me | Theorems.Thm_Groundwork_Prog_SatTopK_length_enc
-- name    : Groundwork.Prog.SatTopK.length_enc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:00.851383+00:00
-- url     : https://prove2.me/theorems/f4ec21b8-161c-4f55-b98f-416c1911d867
-- title:
--   Sat Top K: length enc
-- statement:
--   The length of the code: n + 1 bits for n, then k slots of ⌊log₂(2n)⌋ + 1 bits for every clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Top/Sat.lean#L66-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Top/Sat.lean#L66-L68

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
import Theorems.Thm_Groundwork_Decode_length_enc

set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK
open Groundwork.Sparsify (leaves)

theorem Groundwork.Prog.SatTopK.length_enc (k : ℕ) {n : ℕ} (φ : Sat3.CNF n) :
    (SatK.enc k φ).length = n + 1 + φ.length * (k * (Nat.log2 (2 * n) + 1)) := by sorry
