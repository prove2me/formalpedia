-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Normal_C_rat_smul
-- name    : GeneralPieces.GenF.Normal.C_rat_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:46.598075+00:00
-- url     : https://prove2.me/theorems/41525a11-fd9f-4c44-830c-0eb4fff68ecc
-- title:
--   Normal: C rat smul
-- statement:
--   The Normal construction uses the C rat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L70-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L70-L71

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
variable {Y A : Type} [CommRing A] [Algebra ℚ A]

theorem GeneralPieces.GenF.Normal.C_rat_smul (q : ℚ) (a : A) : MvPowerSeries.C (σ := Y) (q • a) = q • MvPowerSeries.C (σ := Y) a := by sorry
