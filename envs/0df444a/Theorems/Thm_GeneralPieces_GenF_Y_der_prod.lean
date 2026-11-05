-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Y_der_prod
-- name    : GeneralPieces.GenF.Y.der_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:10:14.715398+00:00
-- url     : https://prove2.me/theorems/903b5cad-cb7d-42c4-a554-e92c2c8273b7
-- title:
--   Y: der prod
-- statement:
--   The product rule for a product over a multiset.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L89-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L89-L100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open GeneralPieces.GenF.Y

theorem GeneralPieces.GenF.Y.der_prod {R B ι : Type} [CommRing R] [CommRing B] [Algebra R B] [DecidableEq ι] (d : Derivation R B B) (s : Multiset ι) (f : ι → B) :
    d (s.map f).prod = ∑ k ∈ s.toFinset, s.count k • (d (f k) * ((s.erase k).map f).prod) := by sorry
