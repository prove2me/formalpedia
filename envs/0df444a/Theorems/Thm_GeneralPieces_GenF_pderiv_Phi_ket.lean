-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_Phi_ket
-- name    : GeneralPieces.GenF.pderiv_Phi_ket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:40.510602+00:00
-- url     : https://prove2.me/theorems/19982bb6-85a6-4385-a278-f09b4369e5a6
-- title:
--   Gen F: pderiv Phi ket
-- statement:
--   ∂/∂x_i of e^{A⁻}·e^{B⁻}·t^σ': each factor t_k of t^σ' in turn is replaced by k·C(−k−1,
--   n−1)·u^{−k−n}, or ·v^{−k−n}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L173-L181
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L173-L181

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

theorem GeneralPieces.GenF.pderiv_Phi_ket (rd : Bool) (i : X) (σ' : Multiset ℕ) :
    MvPowerSeries.pderiv Tv i (Phi rd (ket rd σ')) =
      ∑ k ∈ σ'.toFinset, σ'.count k • (embW (MvPowerSeries.C ((k : ℚ) • cS rd i (-(k : ℤ)))) * Phi rd (ket rd (σ'.erase k))) := by sorry
