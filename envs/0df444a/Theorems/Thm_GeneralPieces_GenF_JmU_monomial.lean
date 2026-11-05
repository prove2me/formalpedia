-- Prove2me | Theorems.Thm_GeneralPieces_GenF_JmU_monomial
-- name    : GeneralPieces.GenF.JmU_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:12:06.908205+00:00
-- url     : https://prove2.me/theorems/8b485967-a475-40ad-a9f4-09a5c60983d6
-- title:
--   Gen F: Jm U monomial
-- statement:
--   J_n^-(u) on a monomial.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L45-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L45-L49

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

theorem GeneralPieces.GenF.JmU_monomial (n : ℕ) (τ : Multiset ℕ) : JmU n (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) =
    ∑ k ∈ τ.toFinset, ((τ.count k : Lu) * (C ((k : ℚ) * (bet n (-(k : ℤ)) : ℚ)) * T (-(k : ℤ) - n))) • MvPolynomial.monomial (Multiset.toFinsupp (τ.erase k)) (1 : Lu) := by sorry
