-- Prove2me | Theorems.Thm_Groundwork_abs_sum_powersetCard_le
-- name    : Groundwork.abs_sum_powersetCard_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:26.850505+00:00
-- url     : https://prove2.me/theorems/553d8c8a-19ea-47a0-8a2e-5369f58789d0
-- title:
--   Groundwork: abs sum powerset Card le
-- statement:
--   A sum over the sets S of i positions of products of λ integers of absolute value at most 1 has
--   absolute value at most
--   C(λ,i) ≤ 2^λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Bit.lean#L57-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Bit.lean#L57-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Groundwork_Cross_Bit
set_option autoImplicit false
section
section
open Groundwork
open Finset

theorem Groundwork.abs_sum_powersetCard_le {n : ℕ} (i : ℕ) (f1 f0 : Fin n → ℤ) (h1 : ∀ k, |f1 k| ≤ 1) (h0 : ∀ k, |f0 k| ≤ 1) :
    |∑ S ∈ powersetCard i (univ : Finset (Fin n)), (∏ k ∈ S, f1 k) * ∏ k ∈ Sᶜ, f0 k| ≤ 2 ^ n := by sorry
