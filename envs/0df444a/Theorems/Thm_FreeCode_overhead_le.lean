-- Prove2me | Theorems.Thm_FreeCode_overhead_le
-- name    : FreeCode.overhead_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:45:32.547499+00:00
-- url     : https://prove2.me/theorems/a3ab9011-5710-486e-a179-ae28c0702b35
-- title:
--   Free Code: overhead le
-- statement:
--   The factor of the simulation that is polynomial: for the code x of a k-CNF on n variables and S =
--   c·(n+2)^c, (|x| + S + 1)^q ≤ (2^k·(k+1) + 2 + c)^q·(n+2)^((k+1+c)·q).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Behind.lean#L56-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Behind.lean#L56-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Behind
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat

theorem FreeCode.overhead_le {k n : ℕ} {φ : Sat3.CNF n} (h3 : SatK.IsKCNF k φ) (c q : ℕ) :
    ((SatFree.enc φ).length + c * (n + 2) ^ c + 1) ^ q ≤ (2 ^ k * (k + 1) + 2 + c) ^ q * (n + 2) ^ ((k + 1 + c) * q) := by sorry
