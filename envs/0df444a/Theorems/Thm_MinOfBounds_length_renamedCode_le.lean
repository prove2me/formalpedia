-- Prove2me | Theorems.Thm_MinOfBounds_length_renamedCode_le
-- name    : MinOfBounds.length_renamedCode_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:54:02.253133+00:00
-- url     : https://prove2.me/theorems/2cce3915-c895-4275-a052-4a6124ffc2f3
-- title:
--   Min Of Bounds: length renamed Code le
-- statement:
--   The code of the renamed formula is at most twice as long as the compact code, for a formula with
--   at most k literals in every clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Rename.lean#L80-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Rename.lean#L80-L89

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open MinOfBounds
open Groundwork Groundwork.Decode VariableBound.Rename MainTheoremForms
open Sat3 (CNF)

theorem MinOfBounds.length_renamedCode_le {k V : ℕ} (φ : CNF V) (h : ∀ C ∈ φ, C.length ≤ k) : (renamedCode k φ).length ≤ 2 * (encC k φ).length := by sorry
