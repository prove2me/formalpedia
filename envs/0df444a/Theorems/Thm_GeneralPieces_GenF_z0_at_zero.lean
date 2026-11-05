-- Prove2me | Theorems.Thm_GeneralPieces_GenF_z0_at_zero
-- name    : GeneralPieces.GenF.z0_at_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:34:24.157303+00:00
-- url     : https://prove2.me/theorems/3ec079f3-3ac4-4313-b2fb-e5d990a03018
-- title:
--   Gen F: z0 at zero
-- statement:
--   The Gen F construction uses the z0 at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L112-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L112-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset

theorem GeneralPieces.GenF.z0_at_zero {R : Type} [Zero R] (f : ℕ → R) : z0 f 0 = 0 := by sorry
