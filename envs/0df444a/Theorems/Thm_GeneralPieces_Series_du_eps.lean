-- Prove2me | Theorems.Thm_GeneralPieces_Series_du_eps
-- name    : GeneralPieces.Series.du_eps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:51.810208+00:00
-- url     : https://prove2.me/theorems/c20bbf16-a066-4ec7-9fd1-1ce9389314a5
-- title:
--   Series: du eps
-- statement:
--   Differentiating (u − v)·ε = 1 with respect to u.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L190-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L190-L191

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

theorem GeneralPieces.Series.du_eps : du eps = -eps ^ 2 := by sorry
