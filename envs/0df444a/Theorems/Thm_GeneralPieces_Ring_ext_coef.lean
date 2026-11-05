-- Prove2me | Theorems.Thm_GeneralPieces_Ring_ext_coef
-- name    : GeneralPieces.Ring.ext_coef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:28:43.420733+00:00
-- url     : https://prove2.me/theorems/e0415b5d-5dcc-496e-8011-3afeba1cf32d
-- title:
--   Ring: ext coef
-- statement:
--   Two polynomials with the same coefficients are equal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Basic.lean#L95-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Basic.lean#L95-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.ext_coef {f g : V} (h : ∀ π, coef π f = coef π g) : f = g := by sorry
