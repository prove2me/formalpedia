-- Prove2me | Theorems.Thm_GeneralPieces_Series_kappa_sum
-- name    : GeneralPieces.Series.kappa_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:12.5744+00:00
-- url     : https://prove2.me/theorems/828f40fe-2f10-4533-91f5-a3d3b14461eb
-- title:
--   Series: kappa sum
-- statement:
--   The sum in the display for κ: Σ_{k ≥ 1} k·C(−k−1, j−1)·C(k−1, n−1)·ω₁^{−k−j}·ω₂^{k−n} =
--   Γ_{j,n}·ε₊^{j+n}, "because the sum over k is the left side of (49)".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L444-L446
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L444-L446

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial

theorem GeneralPieces.Series.kappa_sum {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (sumP j n fun k => (k : ℚ) * (Ring.choose (-k - 1) (j - 1) : ℤ) * (Ring.choose (k - 1) (n - 1) : ℤ)) = (ClauseBound.Boson.Gam j n : ℚ) • epsP ^ (j + n) := by sorry
