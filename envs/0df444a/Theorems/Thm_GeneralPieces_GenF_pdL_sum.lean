-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pdL_sum
-- name    : GeneralPieces.GenF.pdL_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:59.476058+00:00
-- url     : https://prove2.me/theorems/394ec452-5ec7-401c-aad3-cae6e4ec07d2
-- title:
--   Gen F: pd L sum
-- statement:
--   The Gen F construction uses the pd L sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L59-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L59-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]

theorem GeneralPieces.GenF.pdL_sum {ι : Type} (L : List Y) (s : Finset ι) (F : ι → MvPowerSeries Y R) : pdL L (∑ j ∈ s, F j) = ∑ j ∈ s, pdL L (F j) := by sorry
