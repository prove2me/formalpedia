-- Prove2me | Theorems.Thm_GeneralPieces_GenF_braW_C_JpU_mul
-- name    : GeneralPieces.GenF.braW_C_JpU_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:10.602224+00:00
-- url     : https://prove2.me/theorems/04fb61cf-aa26-45d0-990d-6d62d75f74b1
-- title:
--   Gen F: bra W C Jp U mul
-- statement:
--   The Gen F construction uses the bra W C Jp U mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L399-L403
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L399-L403

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

theorem GeneralPieces.GenF.braW_C_JpU_mul {σ : Multiset ℕ} {E : ℕ} (h : σ.sum ≤ E) (n : ℕ) (w : W) :
    braW σ (MvPowerSeries.C (HahnSeries.C (JpU E n)) * w) = ∑ l ∈ σ.toFinset, MvPowerSeries.C ((bet n l : ℚ) • mo ((l : ℤ) - n) 0) * braW (σ.erase l) w := by sorry
