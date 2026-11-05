-- Prove2me | Theorems.Thm_GeneralPieces_Series_Qk_eq_sum
-- name    : GeneralPieces.Series.Qk_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:18:34.01798+00:00
-- url     : https://prove2.me/theorems/13c05c29-1ece-47cb-806f-f94c7d3624a7
-- title:
--   Series: Qk eq sum
-- statement:
--   Q_s(a,b) is linear in a, and a^{⟨i⟩} = C(H,i)·a for a monomial a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L55-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L55-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Constant
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_GeneralPieces_Series_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {A : FA} {b : List ℕ}

theorem GeneralPieces.Series.Qk_eq_sum (hA : A.Ok b.sum) (s : ℤ) (π σ : Multiset ℕ) : Qk A b s π σ = (A.map fun c => c.1 * qP c.2 b s π σ).sum := by sorry
