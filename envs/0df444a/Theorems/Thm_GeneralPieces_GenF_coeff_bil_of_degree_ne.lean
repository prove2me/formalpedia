-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_bil_of_degree_ne
-- name    : GeneralPieces.GenF.coeff_bil_of_degree_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:35.263208+00:00
-- url     : https://prove2.me/theorems/a6886299-6f2d-4b98-a0a1-829f0887c958
-- title:
--   Gen F: coeff bil of degree ne
-- statement:
--   The Gen F construction uses the coeff bil of degree ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L94-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L94-L95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
variable {R : Type}

theorem GeneralPieces.GenF.coeff_bil_of_degree_ne [Semiring R] (q : X → X → R) {α : X →₀ ℕ} (h : α.degree ≠ 2) : MvPowerSeries.coeff α (bil q) = 0 := by sorry
