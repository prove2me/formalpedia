-- Prove2me | Theorems.Thm_GraphProblems_runs_of_mapIn
-- name    : GraphProblems.runs_of_mapIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:36:41.646126+00:00
-- url     : https://prove2.me/theorems/1be81ae7-7285-47ca-b760-6b3a52010c3f
-- title:
--   Graph Problems: runs of map In
-- statement:
--   The Graph Problems construction uses the runs of map In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Engine.lean#L77-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Engine.lean#L77-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatStatement
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Value
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_GridLoop
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_Brute
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_ToTuring_Poly_Count
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_Engine
set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat

theorem GraphProblems.runs_of_mapIn {α β γ : Type} {f : α → β} {M : Stepped β γ} {a : α} {t S : ℕ} {c : γ} (h : (Stepped.mapIn f M).Runs a t S c) :
    M.Runs (f a) t S c := by sorry
