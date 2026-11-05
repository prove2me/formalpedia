-- Prove2me | Theorems.Thm_GeneralPieces_Series_d1M_epsM
-- name    : GeneralPieces.Series.d1M_epsM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:06:08.224813+00:00
-- url     : https://prove2.me/theorems/add1c46f-03e2-4914-a7a9-2704e1000d24
-- title:
--   Series: d1 M eps M
-- statement:
--   "Differentiating (ω₁ − ω₂)·ε₋ = 1 gives ∂_{ω₁}ε₋ = −ε₋²".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L219-L221
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L219-L221

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial

theorem GeneralPieces.Series.d1M_epsM : d1M epsM = -epsM ^ 2 := by sorry
