-- Prove2me | Theorems.Thm_GeneralPieces_GenF_z0_of_pos
-- name    : GeneralPieces.GenF.z0_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:34:19.81584+00:00
-- url     : https://prove2.me/theorems/1937fba6-7264-4bc4-96c4-f0e09c21b1ac
-- title:
--   Gen F: z0 of pos
-- statement:
--   The Gen F construction uses the z0 of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L114-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L114-L114

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

theorem GeneralPieces.GenF.z0_of_pos {R : Type} [Zero R] (f : ℕ → R) {n : ℕ} (hn : 1 ≤ n) : z0 f n = f n := by sorry
