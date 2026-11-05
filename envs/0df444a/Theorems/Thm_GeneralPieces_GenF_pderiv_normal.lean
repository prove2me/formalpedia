-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_normal
-- name    : GeneralPieces.GenF.pderiv_normal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:50.709245+00:00
-- url     : https://prove2.me/theorems/52e5b28f-4e04-44a1-bb1d-706412b3ff02
-- title:
--   Gen F: pderiv normal
-- statement:
--   The differential equation of ⟨𝒩⟩ in every variable x_i, for |σ| ≤ E: one term for every
--   different part l of σ, from A⁺ or B⁺, and one for every different part k of σ', from A⁻ or B⁻.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L205-L216
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L205-L216

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

theorem GeneralPieces.GenF.pderiv_normal (rd : Bool) {E : ℕ} {σ : Multiset ℕ} (hσ : σ.sum ≤ E) (σ' : Multiset ℕ) (i : X) :
    MvPowerSeries.pderiv S i (normal rd E σ σ') =
      ∑ l ∈ σ.toFinset, MvPowerSeries.C (cS rd i (l : ℤ)) * normal rd E (σ.erase l) σ' +
        ∑ k ∈ σ'.toFinset, MvPowerSeries.C (((k : ℚ) * σ'.count k) • cS rd i (-(k : ℤ))) * normal rd E σ (σ'.erase k) := by sorry
