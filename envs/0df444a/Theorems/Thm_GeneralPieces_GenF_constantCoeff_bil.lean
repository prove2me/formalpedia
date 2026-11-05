-- Prove2me | Theorems.Thm_GeneralPieces_GenF_constantCoeff_bil
-- name    : GeneralPieces.GenF.constantCoeff_bil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:50.666027+00:00
-- url     : https://prove2.me/theorems/d53acb13-1dbd-47e5-98f9-549947c76e3c
-- title:
--   Gen F: constant Coeff bil
-- statement:
--   The Gen F construction uses the constant Coeff bil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L97-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L97-L99

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

theorem GeneralPieces.GenF.constantCoeff_bil [Semiring R] (q : X → X → R) : MvPowerSeries.constantCoeff (bil q) = 0 := by sorry
