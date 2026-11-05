-- Prove2me | Theorems.Thm_NamesInOrder_polynomialIsBelowTheBound
-- name    : NamesInOrder.polynomialIsBelowTheBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:28:50.208105+00:00
-- url     : https://prove2.me/theorems/89223ebb-4d00-4204-83f9-2ff732c7162e
-- title:
--   Names In Order: polynomial Is Below The Bound
-- statement:
--   So a polynomial in the length of the input is below the bound of the Main Theorem: by
--   `codeIsShort` it is below both polynomials, which are below the two bounds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L193-L201
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L193-L201

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_NamesInOrder_Arith
set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)

theorem NamesInOrder.polynomialIsBelowTheBound : PolynomialIsBelowTheBound := by sorry
