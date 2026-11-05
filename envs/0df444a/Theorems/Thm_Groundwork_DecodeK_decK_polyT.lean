-- Prove2me | Theorems.Thm_Groundwork_DecodeK_decK_polyT
-- name    : Groundwork.DecodeK.decK_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:32:24.393697+00:00
-- url     : https://prove2.me/theorems/2d683c3a-a7b4-4bc8-a9cf-32770159dc06
-- title:
--   Decode K: dec K poly T
-- statement:
--   The decoder `decK k`, which reads the input of the algorithm, is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Poly/Decode.lean#L42-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Poly/Decode.lean#L42-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_WidthK_Decode
import Definitions.Def_WidthK_Poly_Decode
set_option autoImplicit false
section
section
open Groundwork Groundwork.DecodeK
open Groundwork.Decode
variable {α : Type} [Enc α]

theorem Groundwork.DecodeK.decK_polyT (k : ℕ) : PolyT (decK k) := by sorry
