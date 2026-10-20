-- Prove2me | Theorems.Thm_OAI_SingleFold_Counter_System_test_values
-- name    : OAI.SingleFold.Counter.System.test_values
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:43:10.293216+00:00
-- url     : https://prove2.me/theorems/c1655f79-2c22-45d6-934e-5bdd15601c23
-- title:
--   Arc digits at a test step
-- statement:
--   Consider a counter machine with finite sets of states $Q$ and counters $J$ (each instruction halts, increments a counter, or tests a counter and decrements it if nonzero), an input $d\in\mathbb{N}^J$, and a witness $v$ satisfying the counter system: base $B=2^w=4b$, length $k>0$, packed state indicators $\mathrm{state}_q$, packed branch indicators $\mathrm{zero}_q,\mathrm{dec}_q$ of test states, packed counter histories $\mathrm{counter}_j$, and the polynomial and binary-domination conditions linking them. Write $\mathrm{digit}(x,t)=\lfloor x/B^t\rfloor\bmod B$, and let $\mathrm{inc}_j,\mathrm{dec}_j$ be the sums of the arc indicators that increment, resp. decrement, counter $j$. Suppose at time $t$ the state digits single out $q$, i.e. $\mathrm{digit}(\mathrm{state}_p,t)=[p=q]$ for all $p$, and $q$ tests counter $j$ with zero-successor $p_0$ and decrement-successor $p_d$. Then at time $t$:
--   $$
--   \mathrm{digit}(\mathrm{incoming}_z,t)=[z=p_d]\,\mathrm{digit}(\mathrm{dec}_q,t)+[z=p_0]\,\mathrm{digit}(\mathrm{zero}_q,t)\quad\text{for all }z,
--   $$
--   no counter is incremented, and the decrement digit of counter $i$ is $\mathrm{digit}(\mathrm{dec}_q,t)$ if $i=j$ and $0$ otherwise.
--
--   At a test step only the two branches of the active state can be taken. Their indicators are the only nonzero arc digits.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/CounterRecords.lean#L245-L263

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

theorem OAI.SingleFold.Counter.System.test_values (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀p,digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) :
    (∀z,digit v.B (incoming M v z) t=
      (if z=pd then digit v.B (v.decBranch q) t else 0)+
      (if z=p0 then digit v.B (v.zeroBranch q) t else 0)) ∧
    (∀i,digit v.B (increments M v i) t=0) ∧
    (∀i,digit v.B (decrements M v i) t=if i=j then digit v.B (v.decBranch q) t else 0) := by sorry
