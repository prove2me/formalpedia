-- Prove2me | Theorems.Thm_Groundwork_PolyT_len_le_of_le_dbl
-- name    : Groundwork.PolyT.len_le_of_le_dbl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:38:57.538569+00:00
-- url     : https://prove2.me/theorems/616d03a2-f208-46ec-bda5-8e5613c91f16
-- title:
--   Poly T: len le of le dbl
-- statement:
--   A number that is at most 2c + 1 has at most one binary digit more than c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L38-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L38-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.len_le_of_le_dbl {a c : ℕ} (h : a ≤ c + c + 1) : len a ≤ len c + 3 := by sorry
