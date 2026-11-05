-- Prove2me | Theorems.Thm_GeneralPieces_stExpansion_of
-- name    : GeneralPieces.stExpansion_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:17:08.125959+00:00
-- url     : https://prove2.me/theorems/4a8d05d3-1e92-476d-b647-d7fc7cf65233
-- title:
--   General Pieces: st Expansion of
-- statement:
--   The expansion of f₊ and f₋ from display (51): the terms are indexed by the splittings (β, γ) of
--   x^μ·x'^ν, with Γ_c = μ!·ν!·Γ_β, N_c the weight of β, and n_c the coefficient of γ in ⟨𝒩⟩;
--   the number G is μ!·ν!·Γ_{μ,ν}. For monomials of different weights, which the paper does not
--   consider, f₊ = f₋ = 0 and one term with n_c = 0 serves.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L155-L217
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L155-L217

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble
set_option autoImplicit false
section
section
open GeneralPieces
open GeneralPieces.Series GeneralPieces.GenF ClauseBound.Boson MvPowerSeries Finset

theorem GeneralPieces.stExpansion_of (h15 : StTwoOrders) (hN1 : StN1) (hN2 : StN2) (hN3 : StN3) (hY : StY) : StExpansion := by sorry
