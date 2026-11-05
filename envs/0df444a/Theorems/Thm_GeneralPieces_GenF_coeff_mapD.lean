-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_mapD
-- name    : GeneralPieces.GenF.coeff_mapD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:49.428819+00:00
-- url     : https://prove2.me/theorems/cebb33ac-2d5f-4705-a1a7-9703e979ec21
-- title:
--   Gen F: coeff map D
-- statement:
--   The Gen F construction uses the coeff map D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Taylor.lean#L316-L316
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Taylor.lean#L316-L316

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Exp
import Mathlib.Algebra.MvPolynomial.Derivation
import Definitions.Def_GeneralPieces_GenF_Taylor
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]

theorem GeneralPieces.GenF.coeff_mapD (d : Derivation ℚ A A) (f : MvPowerSeries X A) (α : X →₀ ℕ) : coeff α (mapD d f) = d (coeff α f) := by sorry
