-- Prove2me | Theorems.Thm_GeneralPieces_GenF_braW_C_sel_mul
-- name    : GeneralPieces.GenF.braW_C_sel_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:49.737397+00:00
-- url     : https://prove2.me/theorems/80e5dd3d-818e-468e-a5e0-2d7b1a403e02
-- title:
--   Gen F: bra W C sel mul
-- statement:
--   The coefficient of t^σ in (the series beside x_i in A⁺ + B⁺)·w: each factor t_l of t^σ in turn
--   is taken away, with the coefficient C(l−1, n−1)·u^{l−n}, or ·v^{l−n}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L187-L201
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L187-L201

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

theorem GeneralPieces.GenF.braW_C_sel_mul (rd : Bool) {E : ℕ} {σ : Multiset ℕ} (hσ : σ.sum ≤ E) (i : X) (w : W) :
    braW σ (MvPowerSeries.C (sel rd (fun n => HahnSeries.C (JpU E n)) JpV i) * w) = ∑ l ∈ σ.toFinset, MvPowerSeries.C (cS rd i (l : ℤ)) * braW (σ.erase l) w := by sorry
