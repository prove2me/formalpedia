-- Prove2me | Theorems.Thm_MinOfBounds_numOcc_le_mul
-- name    : MinOfBounds.numOcc_le_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:54:04.900935+00:00
-- url     : https://prove2.me/theorems/9b6d1c46-7b05-42a2-bc62-7cc2f816cc8b
-- title:
--   Min Of Bounds: num Occ le mul
-- statement:
--   n ≤ m·k: in a formula with m clauses of at most k literals each, at most m·k variables occur.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Rename.lean#L69-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Rename.lean#L69-L76

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

theorem MinOfBounds.numOcc_le_mul {k V : ℕ} (φ : CNF V) (h : ∀ C ∈ φ, C.length ≤ k) : numOcc φ ≤ φ.length * k := by sorry
