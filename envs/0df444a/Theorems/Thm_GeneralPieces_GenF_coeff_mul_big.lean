-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_mul_big
-- name    : GeneralPieces.GenF.coeff_mul_big
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:32:52.958504+00:00
-- url     : https://prove2.me/theorems/a22b5110-741c-4a4a-bef1-2166a9be0549
-- title:
--   Gen F: coeff mul big
-- statement:
--   The coefficients of a product, as a sum over any two sets that contain the supports.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L130-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L130-L139

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

theorem GeneralPieces.GenF.coeff_mul_big {R : Type} [CommRing R] (f g : HahnSeries ℤ R) {A B : Set ℤ} (hA : A.IsPWO) (hB : B.IsPWO) (hf : f.support ⊆ A) (hg : g.support ⊆ B) (y : ℤ) :
    (f * g).coeff y = ∑ ij ∈ Finset.antidiagonal hA hB y, f.coeff ij.1 * g.coeff ij.2 := by sorry
