-- Prove2me | Theorems.Thm_OAI_SingleFold_Counter_System_decode
-- name    : OAI.SingleFold.Counter.System.decode
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:44:59.447977+00:00
-- url     : https://prove2.me/theorems/49471f47-fc1c-4c57-8c17-e7e0604e5904
-- title:
--   A solution of the counter system encodes the actual run
-- statement:
--   Consider a counter machine with finite sets of states $Q$ and counters $J$ (each instruction halts, increments a counter, or tests a counter and decrements it if nonzero), an input $d\in\mathbb{N}^J$, and a witness $v$ satisfying the counter system: base $B=2^w=4b$, length $k>0$, packed state indicators $\mathrm{state}_q$, packed branch indicators $\mathrm{zero}_q,\mathrm{dec}_q$ of test states, packed counter histories $\mathrm{counter}_j$, and the polynomial and binary-domination conditions linking them. Write $\mathrm{digit}(x,t)=\lfloor x/B^t\rfloor\bmod B$, and let $\mathrm{inc}_j,\mathrm{dec}_j$ be the sums of the arc indicators that increment, resp. decrement, counter $j$. Then for every $t<k$,
--   $$
--   \mathrm{digit}(\mathrm{state}_q,t)=[q=\mathrm{state}(\mathrm{run}(d,t))],\qquad\mathrm{digit}(\mathrm{counter}_j,t)=\mathrm{value}_j(\mathrm{run}(d,t)) .
--   $$
--
--   The digits of any witness are exactly the configurations of the machine's run on input $d$. This is the soundness of the arithmetization.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/CounterRecords.lean#L283-L346

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

theorem OAI.SingleFold.Counter.System.decode (t : ℕ) (ht : t < v.k) :
    (∀q,digit v.B (v.state q) t=if q=(run M d t).state then 1 else 0) ∧
    (∀j,digit v.B (v.counter (some j)) t=(run M d t).value j) := by sorry
