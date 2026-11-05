-- Prove2me | Theorems.Thm_GeneralPieces_GenF_y0_cons
-- name    : GeneralPieces.GenF.y0_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:34:26.752227+00:00
-- url     : https://prove2.me/theorems/32e41a9c-5c4b-4d8a-900b-019a174a70ba
-- title:
--   Gen F: y0 cons
-- statement:
--   The Gen F construction uses the y0 cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L38-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L38-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset

theorem GeneralPieces.GenF.y0_cons (n : ℕ) (a : List ℕ) (σ : Multiset ℕ) (p : Vu) :
    y0 (n :: a) σ p = ∑ l ∈ σ.toFinset, (C (bet n l : ℚ) * T ((l : ℤ) - n)) * y0 a (σ.erase l) p + y0 a σ (JmU n p) := by sorry
