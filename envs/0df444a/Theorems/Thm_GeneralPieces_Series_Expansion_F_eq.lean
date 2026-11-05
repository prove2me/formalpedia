-- Prove2me | Theorems.Thm_GeneralPieces_Series_Expansion_F_eq
-- name    : GeneralPieces.Series.Expansion.F_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:18:46.421823+00:00
-- url     : https://prove2.me/theorems/9d415655-c642-4ece-829c-0a7bce778804
-- title:
--   Expansion: F eq
-- statement:
--   F = Σ_s F_s·ω₁^s·ω₂^{−s}, with F_s = ⟨Q_s(a,b)⟩.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L112-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean#L112-L127

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}

theorem GeneralPieces.Series.Expansion.F_eq (X : Expansion a b G π σ) (hab : a.sum ≤ b.sum) :
    X.F = ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), (qP a b s π σ : ℚ) • W s (-s) := by sorry
