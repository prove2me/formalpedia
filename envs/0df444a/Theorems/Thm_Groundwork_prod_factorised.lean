-- Prove2me | Theorems.Thm_Groundwork_prod_factorised
-- name    : Groundwork.prod_factorised
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:44.486389+00:00
-- url     : https://prove2.me/theorems/6b1be762-64a8-4b8f-8a98-6b615d2d02c9
-- title:
--   Groundwork: prod factorised
-- statement:
--   (a), for a family: a product of factorised functions is factorised over the tuples of labels, by
--   the products of the
--   factors.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L61-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean#L61-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Function
import Definitions.Def_Groundwork_Net_Calculus
set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι X' τ A α : Type*}

theorem Groundwork.prod_factorised [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X') (d : X')
    (f f' : ι → X' → ℤ) :
    ∏ i with P i, ∑ x ∈ T i, f i x * f' i x =
      ∑ t ∈ tuples P T d, (∏ i with P i, f i (t i)) * ∏ i with P i, f' i (t i) := by sorry
