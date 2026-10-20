-- Prove2me | Theorems.Thm_OAI_SingleFold_Counter_System_counter_update
-- name    : OAI.SingleFold.Counter.System.counter_update
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:42:25.485501+00:00
-- url     : https://prove2.me/theorems/cb0150b3-cb11-42a3-8d51-bd7c9a19dff1
-- title:
--   Packed counters follow the increment/decrement rule
-- statement:
--   Consider a counter machine with finite sets of states $Q$ and counters $J$ (each instruction halts, increments a counter, or tests a counter and decrements it if nonzero), an input $d\in\mathbb{N}^J$, and a witness $v$ satisfying the counter system: base $B=2^w=4b$, length $k>0$, packed state indicators $\mathrm{state}_q$, packed branch indicators $\mathrm{zero}_q,\mathrm{dec}_q$ of test states, packed counter histories $\mathrm{counter}_j$, and the polynomial and binary-domination conditions linking them. Write $\mathrm{digit}(x,t)=\lfloor x/B^t\rfloor\bmod B$, and let $\mathrm{inc}_j,\mathrm{dec}_j$ be the sums of the arc indicators that increment, resp. decrement, counter $j$. Then for every counter $j$, $\mathrm{digit}(\mathrm{counter}_j,0)=d_j$, and for all $t<k-1$
--   $$
--   \mathrm{digit}(\mathrm{counter}_j,t+1)+\mathrm{digit}(\mathrm{dec}_j,t)=\mathrm{digit}(\mathrm{counter}_j,t)+\mathrm{digit}(\mathrm{inc}_j,t) .
--   $$
--
--   The single packed update equation of the system thus enforces, time step by time step, that the counter starts at its input value and changes by the increments minus the decrements.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/CounterRecords.lean#L56-L80

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

theorem OAI.SingleFold.Counter.System.counter_update (j : J) :
    digit v.B (v.counter (some j)) 0=d j ∧ ∀t < v.k-1,
    digit v.B (v.counter (some j)) (t+1)+digit v.B (decrements M v j) t=
      digit v.B (v.counter (some j)) t+digit v.B (increments M v j) t := by sorry
