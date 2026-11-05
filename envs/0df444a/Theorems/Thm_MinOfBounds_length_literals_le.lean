-- Prove2me | Theorems.Thm_MinOfBounds_length_literals_le
-- name    : MinOfBounds.length_literals_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:53:58.797228+00:00
-- url     : https://prove2.me/theorems/e955596a-5e81-45ef-ad5f-4bb18fd50b55
-- title:
--   Min Of Bounds: length literals le
-- statement:
--   A list of m clauses with at most k literals each has at most m·k literals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Rename.lean#L59-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Rename.lean#L59-L66

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
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open MinOfBounds
open Groundwork Groundwork.Decode VariableBound.Rename MainTheoremForms
open Sat3 (CNF)

theorem MinOfBounds.length_literals_le {k : ℕ} (ψ : List (List (ℕ × Bool))) (h : ∀ C ∈ ψ, C.length ≤ k) : (ψ.flatMap fun C => C.map fun l => l.1).length ≤ ψ.length * k := by sorry
