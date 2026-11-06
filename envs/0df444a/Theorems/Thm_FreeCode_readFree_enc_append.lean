-- Prove2me | Theorems.Thm_FreeCode_readFree_enc_append
-- name    : FreeCode.readFree_enc_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:46:02.641085+00:00
-- url     : https://prove2.me/theorems/7b220a4b-3c61-4049-b0fd-895e27d79b31
-- title:
--   Free Code: read Free enc append
-- statement:
--   **The reader on a code followed by any bits**: it returns n in unary and φ with numbers as
--   variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L145-L155
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L145-L155

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Mathlib.Tactic
import Definitions.Def_FreeCode_Reader
set_option autoImplicit false
section
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.readFree_enc_append {n : ℕ} (φ : CNF n) (u : List Bool) : readFree (SatFree.enc φ ++ u) = (List.replicate n (), toN φ) := by sorry
