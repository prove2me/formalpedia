-- Prove2me | Theorems.Thm_OccurM_preparation
-- name    : OccurM.preparation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:08:00.05045+00:00
-- url     : https://prove2.me/theorems/057a3c7f-ef98-4e6f-a303-2f769578471b
-- title:
--   Occur M: preparation
-- statement:
--   The two named preparations number the variables that occur, and they are polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Prep.lean#L46-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Prep.lean#L46-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_OccurM_Prep
set_option autoImplicit false
section
section
open OccurM
open Groundwork MainTheoremForms ClausesOccur VariableBound.Rename
open Sat3 (CNF)

theorem OccurM.preparation : PreparationStmt := by sorry
