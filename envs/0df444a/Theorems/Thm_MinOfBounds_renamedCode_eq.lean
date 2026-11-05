-- Prove2me | Theorems.Thm_MinOfBounds_renamedCode_eq
-- name    : MinOfBounds.renamedCode_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:57:30.771748+00:00
-- url     : https://prove2.me/theorems/341c4ced-df0e-456d-9d64-0aa949b3a830
-- title:
--   Min Of Bounds: renamed Code eq
-- statement:
--   The code of the renamed formula is `SatM.enc k (ren φ)`. No hypothesis on k or φ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Rename.lean#L42-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Rename.lean#L42-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_WidthK_Decode
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Dedup
import Definitions.Def_MinOfBounds_Rename
set_option autoImplicit false
section
section
open MinOfBounds
open Groundwork Groundwork.Decode VariableBound.Rename MainTheoremForms
open Sat3 (CNF)

theorem MinOfBounds.renamedCode_eq (k : ℕ) {V : ℕ} (φ : CNF V) : renamedCode k φ = SatM.enc k (ren φ) := by sorry
