-- Prove2me | Theorems.Thm_GeneralPieces_GenF_fac_add_single
-- name    : GeneralPieces.GenF.fac_add_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:21.187121+00:00
-- url     : https://prove2.me/theorems/3a6f55fe-83ca-40ad-8ee6-653e767a189f
-- title:
--   Gen F: fac add single
-- statement:
--   The Gen F construction uses the fac add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Coeff.lean#L34-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Coeff.lean#L34-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Mathlib.Data.Finsupp.Multiset
import Definitions.Def_GeneralPieces_GenF_Coeff
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]

theorem GeneralPieces.GenF.fac_add_single (α : X →₀ ℕ) (i : X) : fac (α + Finsupp.single i 1) = ((α i : ℚ) + 1) * fac α := by sorry
