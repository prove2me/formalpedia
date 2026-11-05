-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_expD_prod
-- name    : GeneralPieces.GenF.pderiv_expD_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:04.63955+00:00
-- url     : https://prove2.me/theorems/b87929d4-3596-4a46-82d9-55bf6838b0eb
-- title:
--   Gen F: pderiv exp D prod
-- statement:
--   ∂/∂x_i of e^𝒪 applied to a product: if ∂f_k/∂x_i + O_i f_k = g_k and e^𝒪 fixes g_k, each factor
--   in turn is replaced by g_k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L75-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L75-L87

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
variable {Y A : Type} [CommRing A] [Algebra ℚ A]

theorem GeneralPieces.GenF.pderiv_expD_prod {D : Y → Derivation ℚ A A} (hc : ∀ i j a, D i (D j a) = D j (D i a)) (i : Y) {ι : Type} [DecidableEq ι] (s : Multiset ι)
    (f g : ι → MvPowerSeries Y A) (hf : ∀ k, MvPowerSeries.pderiv A i (f k) + mapD (D i) (f k) = g k) (hg : ∀ k, expD D (g k) = g k) :
    MvPowerSeries.pderiv A i (expD D (s.map f).prod) = ∑ k ∈ s.toFinset, s.count k • (g k * expD D ((s.erase k).map f).prod) := by sorry
