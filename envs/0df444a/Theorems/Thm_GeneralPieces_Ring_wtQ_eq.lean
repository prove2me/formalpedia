-- Prove2me | Theorems.Thm_GeneralPieces_Ring_wtQ_eq
-- name    : GeneralPieces.Ring.wtQ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:01:36.294187+00:00
-- url     : https://prove2.me/theorems/da7b6b92-2c74-4333-acda-17cde036c675
-- title:
--   Ring: wt Q eq
-- statement:
--   The products of binomial coefficients are the same.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L192-L201
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L192-L201

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.wtQ_eq (μ : List ℕ+) (ks : List ℤ) : wtQ μ ks = ClauseBound.Boson.wt (toL μ) ks := by sorry
