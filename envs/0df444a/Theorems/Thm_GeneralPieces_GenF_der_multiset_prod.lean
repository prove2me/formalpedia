-- Prove2me | Theorems.Thm_GeneralPieces_GenF_der_multiset_prod
-- name    : GeneralPieces.GenF.der_multiset_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:03.330451+00:00
-- url     : https://prove2.me/theorems/95ee86a6-87b7-402c-8e85-6043b03f0707
-- title:
--   Gen F: der multiset prod
-- statement:
--   The product rule for a product over a multiset.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L39-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L39-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

theorem GeneralPieces.GenF.der_multiset_prod {B ι : Type} [CommRing B] [DecidableEq ι] (d : B →+ B) (hd : ∀ a b, d (a * b) = a * d b + d a * b) (s : Multiset ι) (f : ι → B) :
    d (s.map f).prod = ∑ k ∈ s.toFinset, s.count k • (d (f k) * ((s.erase k).map f).prod) := by sorry
