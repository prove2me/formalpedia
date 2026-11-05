-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Y2
-- name    : GeneralPieces.GenF.Y2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:29:27.741936+00:00
-- url     : https://prove2.me/theorems/54d24a62-c51f-4345-a2c7-0f3e8625c733
-- title:
--   Gen F: Y2
-- statement:
--   "e^{A⁺}e^{A⁻} = Σ_μ x^μ·Y(t^μ, ω₁)/μ!": the derivative of ⟨e^{A⁺}e^{A⁻}·w⟩ with respect to the
--   variables x_n, n in a, has the constant term ⟨t^σ| Y(a, u) w₀⟩, w₀ the constant term of w, if w does
--   not
--   depend on the variables of the inner family. By `borel_zero` this is μ! times the coefficient of
--   x^μ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L152-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L152-L171

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

theorem GeneralPieces.GenF.Y2 (rd : Bool) (E : ℕ) (a : List ℕ) : Pos a → ∀ (σ : Multiset ℕ) (w : W), σ.sum ≤ E → (∀ n, MvPowerSeries.pderiv Tv (xi rd n) w = 0) →
    MvPowerSeries.constantCoeff (pdL (a.map (xi rd)) (GG rd E σ w)) = (MvPowerSeries.constantCoeff w).map (y0 a σ) := by sorry
