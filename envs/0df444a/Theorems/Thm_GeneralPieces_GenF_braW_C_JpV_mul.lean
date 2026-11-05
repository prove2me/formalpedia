-- Prove2me | Theorems.Thm_GeneralPieces_GenF_braW_C_JpV_mul
-- name    : GeneralPieces.GenF.braW_C_JpV_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:06:31.278711+00:00
-- url     : https://prove2.me/theorems/f353fb7a-2da3-45b3-a236-0aa83a1c0b8c
-- title:
--   Gen F: bra W C Jp V mul
-- statement:
--   The Gen F construction uses the bra W C Jp V mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L394-L397
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L394-L397

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

theorem GeneralPieces.GenF.braW_C_JpV_mul (σ : Multiset ℕ) (n : ℕ) (w : W) :
    braW σ (MvPowerSeries.C (JpV n) * w) = ∑ l ∈ σ.toFinset, MvPowerSeries.C ((bet n l : ℚ) • mo 0 ((l : ℤ) - n)) * braW (σ.erase l) w := by sorry
