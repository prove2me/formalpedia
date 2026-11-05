-- Prove2me | Theorems.Thm_NamesInOrder_boundInMWithoutThePolynomial
-- name    : NamesInOrder.boundInMWithoutThePolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:28:33.646134+00:00
-- url     : https://prove2.me/theorems/009aa321-74be-4019-b725-da315aafe65a
-- title:
--   Names In Order: bound In MWithout The Polynomial
-- statement:
--   EVERY machine that meets the bound in m with a polynomial in the length of the input added meets
--   it with nothing added, with another constant: by `codeIsShort` the length is at most 6·(km)², and by
--   `polynomialIsBelowTheBoundInM` the polynomial is below the bound in m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L258-L272
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L258-L272

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

theorem NamesInOrder.boundInMWithoutThePolynomial : BoundInMWithoutThePolynomial := by sorry
