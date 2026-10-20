-- Prove2me | Theorems.Thm_OAI_SingleFold_Counter_System_haltsAt
-- name    : OAI.SingleFold.Counter.System.haltsAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:46:24.042587+00:00
-- url     : https://prove2.me/theorems/3324fc1e-a4fa-4b47-81fc-b18ed42a482f
-- title:
--   A solution of the counter system forces halting at time $k-1$
-- statement:
--   Consider a counter machine with finite sets of states $Q$ and counters $J$ (each instruction halts, increments a counter, or tests a counter and decrements it if nonzero), an input $d\in\mathbb{N}^J$, and a witness $v$ satisfying the counter system: base $B=2^w=4b$, length $k>0$, packed state indicators $\mathrm{state}_q$, packed branch indicators $\mathrm{zero}_q,\mathrm{dec}_q$ of test states, packed counter histories $\mathrm{counter}_j$, and the polynomial and binary-domination conditions linking them. Write $\mathrm{digit}(x,t)=\lfloor x/B^t\rfloor\bmod B$, and let $\mathrm{inc}_j,\mathrm{dec}_j$ be the sums of the arc indicators that increment, resp. decrement, counter $j$. Then the machine, started at its start state with input $d$, halts at time $k-1$:
--   $$
--   \mathrm{state}(\mathrm{run}(d,k-1))=\mathrm{halt},\qquad\mathrm{state}(\mathrm{run}(d,t))\ne\mathrm{halt}\ \text{ for }t<k-1 .
--   $$
--
--   So the counter system has a solution only if the machine halts on $d$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/CounterRecords.lean#L347-L359

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine

open OAI OAI.SingleFold OAI.SingleFold.Counter OAI.SingleFold.Counter.System
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
variable (h : System M d v)
include h
attribute [local instance] Classical.propDecidable

theorem OAI.SingleFold.Counter.System.haltsAt : HaltsAt M d (v.k-1) := by sorry
