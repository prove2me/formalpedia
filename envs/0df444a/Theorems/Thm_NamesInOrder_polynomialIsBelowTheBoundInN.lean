-- Prove2me | Theorems.Thm_NamesInOrder_polynomialIsBelowTheBoundInN
-- name    : NamesInOrder.polynomialIsBelowTheBoundInN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:27:09.630924+00:00
-- url     : https://prove2.me/theorems/3e9659b0-6200-42f8-82f8-362b14e59859
-- title:
--   Names In Order: polynomial Is Below The Bound In N
-- statement:
--   A power of k·(2n+1)^(k+3) is below the bound in n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L185-L186
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L185-L186

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

theorem NamesInOrder.polynomialIsBelowTheBoundInN : PolynomialIsBelowTheBoundInN := by sorry
