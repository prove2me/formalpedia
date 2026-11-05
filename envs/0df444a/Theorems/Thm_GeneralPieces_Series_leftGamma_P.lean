-- Prove2me | Theorems.Thm_GeneralPieces_Series_leftGamma_P
-- name    : GeneralPieces.Series.leftGamma_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:11.189293+00:00
-- url     : https://prove2.me/theorems/1d78ddc2-e82f-4cd0-8e5d-16cd5156c14d
-- title:
--   Series: left Gamma P
-- statement:
--   "The sum over k is the left side of (49)", in 𝓛₊: differentiating Σ_k k·ω₁^{−k−1}·ω₂^{k−1} term
--   by term.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L415-L426
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L415-L426

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

theorem GeneralPieces.Series.leftGamma_P {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (1 / (((j - 1).factorial : ℚ) * ((n - 1).factorial : ℚ))) • d1P^[j - 1] (d2P^[n - 1] (epsP ^ 2)) =
      sumP j n fun k => (k : ℚ) * (Ring.choose (-k - 1) (j - 1) : ℤ) * (Ring.choose (k - 1) (n - 1) : ℤ) := by sorry
