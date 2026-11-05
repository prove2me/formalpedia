-- Prove2me | Theorems.Thm_GeneralPieces_GenF_braW_C_lin_mul
-- name    : GeneralPieces.GenF.braW_C_lin_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:08.279482+00:00
-- url     : https://prove2.me/theorems/ac121145-b053-40fd-b480-5cd2f3a38693
-- title:
--   Gen F: bra W C lin mul
-- statement:
--   The rule `bra_lin_mul` for power series.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L388-L392
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L388-L392

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

theorem GeneralPieces.GenF.braW_C_lin_mul {g : Tv} (hg : Lin1 g) (σ : Multiset ℕ) (w : W) :
    braW σ (MvPowerSeries.C g * w) = ∑ l ∈ σ.toFinset, MvPowerSeries.C (bra {l} g) * braW (σ.erase l) w := by sorry
