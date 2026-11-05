-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_rhs
-- name    : GeneralPieces.GenF.coeff_rhs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:27.206881+00:00
-- url     : https://prove2.me/theorems/6a48afdf-23fe-4cef-ab53-4e636c54c0ff
-- title:
--   Gen F: coeff rhs
-- statement:
--   The coefficient at γ of the right side of the differential equation.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L77-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L77-L83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_NormalL
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson

theorem GeneralPieces.GenF.coeff_rhs (rd : Bool) (E : ℕ) (σ σ' : Multiset ℕ) (i : X) (γ : X →₀ ℕ) :
    MvPowerSeries.coeff γ (∑ l ∈ σ.toFinset, MvPowerSeries.C (cS rd i l) * normal rd E (σ.erase l) σ' +
      ∑ k ∈ σ'.toFinset, MvPowerSeries.C (((k : ℚ) * σ'.count k) • cS rd i (-(k : ℤ))) * normal rd E σ (σ'.erase k)) =
    ∑ l ∈ σ.toFinset, cS rd i l * MvPowerSeries.coeff γ (normal rd E (σ.erase l) σ') +
      ∑ k ∈ σ'.toFinset, (((k : ℚ) * σ'.count k) • cS rd i (-(k : ℤ))) * MvPowerSeries.coeff γ (normal rd E σ (σ'.erase k)) := by sorry
