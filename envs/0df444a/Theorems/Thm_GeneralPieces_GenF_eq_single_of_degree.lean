-- Prove2me | Theorems.Thm_GeneralPieces_GenF_eq_single_of_degree
-- name    : GeneralPieces.GenF.eq_single_of_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:48.681585+00:00
-- url     : https://prove2.me/theorems/5cd6e9cb-0261-4ebb-990f-9adc331b680b
-- title:
--   Gen F: eq single of degree
-- statement:
--   An exponent of degree 1 is that of a variable.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L170-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L170-L178

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

theorem GeneralPieces.GenF.eq_single_of_degree {Y : Type} {m : Y →₀ ℕ} (h : m.degree = 1) : ∃ l, m = Finsupp.single l 1 := by sorry
